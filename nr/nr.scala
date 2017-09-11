/** Copyright 2017 Nebulas
  *
  * Permission is hereby granted, free of charge, to any person obtaining a copy of this software and associated documentation files (the "Software"), to deal in the Software without restriction, including without limitation the rights to use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is furnished to do so, subject to the following conditions:
  *
  * The above copyright notice and this permission notice shall be included in all copies or substantial portions of the Software.
  *
  * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
  */

import java.io._
import org.apache.spark.graphx.{Edge, Graph, VertexId}
import org.apache.spark.rdd.RDD
import breeze.stats.distributions.Gaussian
import scala.reflect.ClassTag
import org.apache.spark.{HashPartitioner, SparkConf, SparkContext}


/** define constants */
val wd = "/data/"
val alpha = 2
val beta = 0.1
val mu = 0.01
val lambda = 2
val topK = 2
val GND = "ground"
val txFile = "txs.txt"
val resultFile = "nr.txt"

val originalTxs = sc.textFile(wd+txFile).map(_.split(",").map(x => x.trim)).
filter(x => x(0).toLong == 0).map(x => (x(1) -> x(2)) -> (x(4).toDouble, x(3).toLong))

def compute(originalTxs:RDD[((String,String),(Double, Long))], sc: org.apache.spark.SparkContext ):Unit = {

def writeToFile(fileName: String, text: String): Unit = {
  val file = new File(wd + fileName)
  val bw = new BufferedWriter(new FileWriter(file))
  bw write text
  bw.close()
}

def addressesOfTxs[A: ClassTag, B: ClassTag](txs: RDD[((A, A), B)]): RDD[A] = {
  txs.flatMap(x => List(x._1._1, x._1._2)).distinct
}

def stats(allTxs: RDD[((String, String), Double)]): (RDD[(String, Double)], RDD[(String, Double)]) = {
  val nodes = addressesOfTxs(allTxs)
  val zero = nodes.map(x => x -> 0.0)
  val statIn = allTxs.map { case ((s, t), a) => t -> a }.groupByKey.map { case (x, as) => x -> as.toSeq.sum }
  val statOut = allTxs.map { case ((s, t), a) => s -> a }.groupByKey.map { case (x, as) => x -> as.toSeq.sum }

  val out_amounts = zero.leftOuterJoin(statOut).map{ x => x._2._2 match {
    case Some(_Double) => x._1 -> x._2._2.get
    case None => x._1 -> x._2._1
  }}
  val in_amounts = zero.leftOuterJoin(statIn).map { x => x._2._2 match {
    case Some(_Double) => x._1 -> x._2._2.get
    case None => x._1 -> x._2._1
  }}

  (out_amounts, in_amounts)
}

def encourage(in: Double, out: Double): Double = {
  val mu1 = 0.33
  val sigma1 = (-mu1 + 0.5) / 3
  val mu2 = 1.0
  val sigma2 = (mu2 - 0.5) / 3

  val o_io = out / (in + out)

  val n1 = Gaussian(mu1, sigma1).pdf(o_io)
  val n2 = Gaussian(mu2, sigma2).pdf(o_io)
  n1 + n2 * sigma2 / sigma1
}

def normalize(unNormed:RDD[(String, Double)]):RDD[(String, Double)] = {
  val max = unNormed.map(_._2).max
  unNormed.map(x => x._1 -> x._2 / max)
}

def getCoinage(filteredTxsDated:RDD[((String,String), (Double,Long))]):RDD[(String, Double)] = {
  val genesis = filteredTxsDated.map { case ((s, t), (a, ts)) => ts }.min
  val coinage = filteredTxsDated.flatMap { case ((s, t), (a, ts)) => List(t -> (ts, a, "in"), s -> (ts, a, "out")) }.
    groupByKey.map { case (x, txs) => x -> txs.toList.sortBy(_._1) }.map(x => x._1 -> x._2.foldLeft((0.0, 0.0, genesis)) {
    case ((p, b, l), (s, a, k)) => (p + (s - l) * b + (if ((if (k == "in") b + a else b - a) < 0) (a - b) * (s - genesis) else 0.0), List(if (k == "in") b + a else b - a, 0.0).max, s)}._1)
  normalize(coinage)
}

def getRealBalance(filteredTxsDated:RDD[((String,String), (Double,Long))]):RDD[(String, Double)] = {
  val realBalance = filteredTxsDated.flatMap { case ((s, t), (a, ts)) => List(t -> (ts, a, "in"), s -> (ts, a, "out")) }.
    groupByKey.map { case (x, txs) => x -> txs.toList.sortBy(_._1) }.map(x => x._1 -> x._2.foldLeft( (0.0, 0.0)) {
    case ( (bm, b), (s, a, k)) => {val nb = List(if (k == "in") b + a else b - a, 0.0).max; (List(nb,bm).max, nb) } }._1)
  normalize(realBalance)
}

def getEncouragement(filteredTxs:RDD[((String,String), Double)]):RDD[(String, Double)] = {
  val (out, in) = stats(filteredTxs)
  val encouragement: RDD[(String, Double)] = in.join(out).map { case (v, (i, o)) => v -> encourage(i, o) }
  normalize(encouragement)
}

def rank(groundedEdges: RDD[((String, String), Double)]): (RDD[(String, Double)]) = {
  val nodes = addressesOfTxs(groundedEdges)
  val outEdge = groundedEdges.map{case ((s,t),a) => s -> (t , a) }
  val outAmount = outEdge.groupByKey.map(x => x._1 -> x._2.map(y=>y._2).sum)
  val prob = outEdge.join(outAmount).map{case (s, ((t, a), o)) => s -> (t, a / o) }.groupByKey.partitionBy(new HashPartitioner(100)).persist()

  val N = nodes.count
  var ranks = nodes.filter(u => u != GND).map(u => u -> (1.0 / N) )

  for (i <- 1 to 100){
    ranks = prob.join(ranks).flatMap{ case (s, ( l, r )) => l.map{case (t, p) => t -> (p * r) }}.reduceByKey(_ + _)
  }

  val result = ranks
  result.cache()

  val gndScore = result.filter(x => x._1 == GND).take(1).last._2

  result.filter(x => x._1 != GND).map{case (v,r) => v -> (r + gndScore / N)}
}

def idxFormat(txs: RDD[((String, String), Double)]): (RDD[((Long, Long), Double)], RDD[(Long, String)]) = {
  val uid2nid = addressesOfTxs(txs).zipWithIndex().map { case (x, i) => x -> (i + 1) }
  val idxedTxs = txs.map { case ((s, t), a) => s -> (t -> a) }.join(uid2nid).map { case (s, ((t, a), snid)) => t -> (snid, a) }.join(uid2nid).map { case (t, ((s, a), tnid)) => (s, tnid) -> a }
  (idxedTxs, uid2nid.map(x => x._2 -> x._1) )
}

def limit(reducedEdge: RDD[((String,String), Double)]): RDD[((String, String), Double)] = {
  val (out2, in2) = stats(reducedEdge)
  val limitedEdge = reducedEdge.map { case ((s, t), a) => t -> (s, a) }.
    join(out2).join(in2).map { case (t, (((s, a), o), i)) => (s, t) -> a * List(i, o).min / i }.filter(_._2 > 0)
  limitedEdge
}

def wgc(limitedEdge:RDD[((String,String), Double)]): RDD[((String, String), Double)] = {
  val (idxedEdgesAll, nid2uid) = idxFormat(limitedEdge)
  val edgex: RDD[Edge[Double]] = idxedEdgesAll.map { case ((s, t), a) => Edge(s, t, a) }
  val nodex: RDD[(VertexId, String)] = nid2uid
  val graph = Graph(nodex, idxedEdgesAll.map { case ((s, t), a) => Edge(s, t, a) })
  val ucc = graph.connectedComponents().vertices
  val uid2cid = ucc.map { case (x, i) => x.toLong -> i.toLong }.join(nid2uid).map{case (n, (c,u)) => u -> c}
  uid2cid.cache()
  val ccSize = ucc.map { case (v, i) => i -> v }.groupByKey().map { case (i, l) => i -> l.toSeq.size }
  val max_id = ccSize.collect.maxBy(_._2)._1.toLong
  val wgcEdges = limitedEdge.map{case ((s, t), a) => s -> (t, a) }.join(uid2cid).filter { case (s, ((t, a), cid)) => cid == max_id }.map { case (s, ((t, a), cid)) => t -> (s -> a) }.join(uid2cid).filter { case (t, ((s, a), cid)) => cid == max_id }.map { case (t, ((s, a), cid)) => (s -> t) -> a }
  wgcEdges
}

def addGnd(wgcEdges:RDD[((String,String), Double)]): RDD[((String,String), Double)] = {
  val (out3, in3) = stats(wgcEdges)
  val total_io = in3.map(_._2).collect.sum
  val N = addressesOfTxs(wgcEdges).count()

  val avg_io = wgcEdges.map(_._2).sortBy(x=>x).collect.take(wgcEdges.collect.length/2).last

  // surplus + altruist
  val ngToGnd = out3.join(in3).map { case (v, (o, i)) => (v -> GND ) -> (alpha * avg_io + mu * List(i - o, 0).max) }
  // charity + bonus
  val n_ngFromGnd = in3.map { case (v, i) => (GND -> v) -> (beta * avg_io + lambda * math.pow(i,0.8) ) }

  // reduce out from ground
  val totalToGnd = ngToGnd.map { case ((s, t), a) => a }.collect.sum
  val totalFromGnd = n_ngFromGnd.map { case ((s, t), a) => a }.collect.sum
  val ngFromGnd = n_ngFromGnd.map { case ((s, t), a) => (s -> t) -> (totalToGnd * a / totalFromGnd) }

  // edges
  val ngEdges = wgcEdges.union(ngToGnd).union(ngFromGnd)

  ngEdges
}

/** filter valid txs */
val filteredTxsDated = originalTxs.filter { case ((s, t), (a, ts)) => s != t && a > 0 }
val filteredTxs = filteredTxsDated.map { case ((s, t), (a, ts)) => (s -> t) -> a }

/** weigh by top */
val groupedEdge = filteredTxs.groupByKey.map { case (e, as) => e -> as.toList.sorted.reverse.take(topK).sum }

/** coinage, realBalance, encouragement */
val coinage = getCoinage(filteredTxsDated)
val realBalance = getRealBalance(filteredTxsDated)
val encouragement = getEncouragement(filteredTxs)

/** reduce */
val reducedEdge = groupedEdge.map { case ((s, t), a) => t -> (s, a) }.
  join(coinage).join(encouragement).join(realBalance).
    map { case (t, ((((s, a), c ), e), b )) => (s, t) -> a * (  List(c, b).min * e ) }

/** limit */
val limitedEdge = limit(reducedEdge)

/** wgc */
val wgcEdges = wgc(limitedEdge)


/** add gnd node */
val ngEdges = addGnd(wgcEdges)

/** rank */
val lr = rank(ngEdges).sortBy(-_._2)
writeToFile(resultFile, lr.map{case (v,r) => v + "\t" + r.toString}.collect.mkString("\n"))
}


compute(originalTxs, sc)
