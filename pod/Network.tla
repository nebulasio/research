------------------------------ MODULE Network ------------------------------
(**************************************************************************)
(* We need a separate network layer. In this layer, we formalize two *)
(* features of Nebulas network: *)
(* 1. message may be reordered, *)
(* 2. message may be lost. *)
(**************************************************************************)
EXTENDS Naturals
CONSTANT Message
CONSTANT endpoint

VARIABLES trans_buffer, \* messages need to transfer
          recv_buffer   \* received messages

-----------------------------------------------------------------------------
NetworkTypeOK == /\ trans_buffer \in [endpoint -> SUBSET Message]
                 /\ recv_buffer \in [endpoint -> SUBSET Message]

NetworkInit == /\ trans_buffer = [v \in endpoint |-> {}]
               /\ recv_buffer = [v \in endpoint |-> {}]
    
Send(target, msg) == \* put the message into trans_buffer
     /\ trans_buffer' = [trans_buffer EXCEPT ![target] = trans_buffer[target] \cup {msg}]
     /\ UNCHANGED <<endpoint, recv_buffer>>
               
Broadcast(from, msg) == 
(* broadcast the msg to all enpoints, however, we won't make sure all of them recv the msg *)
            \A p \in endpoint \ {from}: Send(p, msg)
              
Recv(target) == \* move the message from trans_buffer to recv_buffer, or just delete it
     \E msg \in trans_buffer[target]:
        \/  /\ recv_buffer' = [recv_buffer EXCEPT ![target] = recv_buffer[target] \cup{msg}]
            /\ trans_buffer' = [trans_buffer EXCEPT ![target] = trans_buffer[target] \ {msg}]
        \/  /\ trans_buffer' = [trans_buffer EXCEPT ![target] = trans_buffer[target] \ {msg}]
            /\ UNCHANGED << recv_buffer>>

RecvedMsgs(e) == recv_buffer[e]

RemoveMsg(e, msg) == /\ recv_buffer' = [recv_buffer EXCEPT![e] = recv_buffer[e] \{msg}]
                     /\ UNCHANGED<<trans_buffer>>
                     
-----------------------------------------------------------------------------
NetworkNext == \E e \in endpoint: Recv(e)
               
NetworkSpec == NetworkInit /\ [][NetworkNext]_<< trans_buffer, recv_buffer>> 

-----------------------------------------------------------------------------
THEOREM NetworkSpec => []NetworkTypeOK

=============================================================================
\* Modification History
\* Last modified Sat Feb 03 16:20:39 CST 2018 by xuepeng
\* Created Sat Jan 27 16:40:51 CST 2018 by xuepeng
