-------------------------- MODULE LocalBlockChain --------------------------
(**************************************************************************)
(* This is for the block chain info in one node.   *)
(* The very basic constraint here is that there is only one root node, i.e., *)
(* the genisis node.  *)
(* Another two constains shall be : *)
(* 1. Two final blocks must be on the same branch; *)
(* 2. Two blocks with the same proposer, or committer, must be on the same branch. *)
(* In the PoD implementation, the 1st constraint is true for good node, while the *)
(* 2nd can be archieved by deposit. *)
(**************************************************************************)
EXTENDS Naturals, Sequences

CONSTANT Validator

VARIABLE UsedIds

VARIABLES Self

VARIABLE block,
         block_prepares,
         block_commits
       
Block == [parent: Nat, 
          id: Nat, 
          proposer: Validator, 
          state: {"init", "prepared", "committed"}]
         \cup
          [val:"genisis", state : "committed", id : 0, proposer: "0"]
          
-----------------------------------------------------------------------------
(********************Helpers *******************************)

NextBlock[n \in block] == CHOOSE v \in block : v.parent = n.id

PrevBlock[n \in block] == CHOOSE v \in block : n.parent = v.id

TailBlock[n \in block] == IF \E t \in block : t.parent = n.id 
                          THEN TailBlock[NextBlock[n] ]
                          ELSE n
                          
FollowingBlock[n \in block] == {n} \cup IF \E t \in block : t.parent = n.id
                                        THEN FollowingBlock[NextBlock[n] ]
                                        ELSE {}
                                                                 
GenisisBlock == [val |-> "genisis", state |-> "committed", id |-> 0, proposer |-> "0"]

AllTails == {t \in block: TailBlock[t] = t}

ChainWithTail[n \in block] == IF n.id = 0 
                                   THEN {n} 
                                   ELSE {n} \cup ChainWithTail[PrevBlock[n] ]
   
AllChains == {ChainWithTail[t] : t \in AllTails}

BlockContributer[n \in block] == IF n.id = 0 THEN {}
                                             ELSE {n.proposer} \cup n.prepares \cup {n.commits} 
                                             
BlockPrepares[n \in block] == block_prepares[n.id]
BlockCommits[n \in block] == block_commits[n.id]
                                                                                          
(* FindContributedTail. We don't have this helper for performance reason. *)
                                
-----------------------------------------------------------------------------
(*********************************Actions ************************)
BCTypeOK == /\ block \subseteq Block
            /\ Self \in Validator
            
BCInit == /\ block = {GenisisBlock}
          /\ block_prepares = [id \in Nat |-> {}]
          /\ block_commits = [id \in Nat |-> {}]

BCGenBlockWithTail(tail) == [parent |-> tail.id,
               id |-> CHOOSE t : t\in Nat /\ t \notin UsedIds,
               proposer |-> Self,
               state |-> "init"]

BCAddBlock(b) == block \cup {b}

BCChangeBlockStatus(b, new_status) == block' = block \ {b} 

BCPrepareBlock(b, v) == [block_prepares EXCEPT![b.id] = block_prepares[b.id] \cup {v}]

BCCommitBlock(b, v) == [block_commits EXCEPT![b.id] = block_commits[b.id] \cup {v}]

----------------------------------------------------------------------------
(********************************** Consistency *************)

(* For a block chain, the final status consistency requirement is like this:    *)
(* If two blocks are committed, they must be on the same branch. *)
BCFinalStatusConsistency == \A a, b \in {t \in block : t.state = "committed"}:
                                FollowingBlock[a] \cap FollowingBlock[b] # {}

(* We define a block's contributor as the validator who propose, prepare or commit *)
(* the block. Then the requirement is like this:   *)
(* For any two blocks, a and b, in which a and b belong to different branches,  *)
(* a's contributer must not be b's contributer.   *)
BCContributerConsistency == \A ch1, ch2 \in AllChains : 
                                LET dch1 == ch1 \ (ch1 \cap ch2) 
                                    dch2 == ch2 \ (ch1 \cap ch2)
                                IN \A b1 \in dch1, b2 \in dch2 :
                                    BlockContributer[b1] \cap BlockContributer[b2] = {}
                                    
BCConsistency == \/ BCFinalStatusConsistency
                 \/ BCContributerConsistency

=============================================================================
\* Modification History
\* Last modified Sat Feb 03 17:47:34 CST 2018 by xuepeng
\* Created Sat Jan 27 16:13:27 CST 2018 by xuepeng
