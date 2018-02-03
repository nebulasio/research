-------------------------------- MODULE POD --------------------------------
EXTENDS Naturals

CONSTANT Validator
 
VARIABLES     
(***********These are the variables in other modules **********************)
          trans_buffer, \* messages need to transfer
          recv_buffer,   \* received messages
          blocks, \* all blocks for all validators
          v_status,
          UsedIds,
          v_block_prepares,
          v_block_commits,
          v_contributed_block
          
VARIABLES 
(***********These are the variables in this module **********************)
          dynasty_status \* dynasty count, this is an increasing number
          
Message ==
  (*************************************************************************)
  
  (* The set of all possible messages.  The ins field indicates the sender. For "propose" *)
  (* message, the "val" field means she propose a block. Since we do not mind the proposed value, we do not *)
  (* record the proposed value here. The "sender" field indicates the sender of a message.   *)
  (*************************************************************************)
  [type : {"propose"}, val : Validator, sender: Validator] 
      \cup
  [type : {"prepare"}, val : Validator, sender : Validator] 
      \cup
  [type : {"vote"}, val : Validator, sender: Validator]
  

Network == INSTANCE Network WITH Message <- Message, endpoint <-Validator,
                                    trans_buffer <- trans_buffer,
                                    recv_buffer <- recv_buffer
        
BlockValidator(n) == INSTANCE PODValidator WITH Validator <- Validator,
                                               Self <- n,
                                               block <- blocks[n],
                                               status <- v_status[n],
                                               UsedIds <- UsedIds,
                                               block_prepares <- v_block_prepares[n],
                                               block_commits <- v_block_commits[n],
                                               contributed_block <- v_contributed_block[n]
                                            
                                               
-----------------------------------------------------------------------------
PODTypeOK == /\ Network!NetworkTypeOK
             /\ \A n \in Validator : BlockValidator(n)!PVTypeOK
             
PODInit == /\ Network!NetworkInit 
           /\ \A n \in Validator: BlockValidator(n)!PVInit
           

-----------------------------------------------------------------------------
(*****************Actions *************************************************)
GotoNextPeriod == \/ \E n \in Validator: BlockValidator(n)!AlreadyReachFinalityStatus
                  \/ \A n \in Validator: BlockValidator(n)!IsImpossibleToReachCommitStatus

-----------------------------------------------------------------------------

PODNext == \/ \E n \in Validator: BlockValidator(n)!PVNext
           \/ Network!NetworkNext
           \/ GotoNextPeriod

=============================================================================
\* Modification History
\* Last modified Sat Feb 03 19:37:48 CST 2018 by xuepeng
\* Created Sat Jan 27 18:04:58 CST 2018 by xuepeng
