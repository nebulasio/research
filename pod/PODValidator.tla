---------------------------- MODULE PODValidator ----------------------------
(* This module defines the behavior of each validator. *)

CONSTANT Validator
VARIABLE Self

VARIABLES     
(***********These are the variables in other modules **********************)
          trans_buffer, \* messages need to transfer
          recv_buffer,   \* received messages
          block, \* all blocks for all validators
          status, \* status of current validator, will be reset at the beginning of each period
          UsedIds, \* all used IDs
          block_prepares,
          block_commits
          
          
VARIABLES
        contributed_block 
        (* All blocks that Self contributed, i.e., proposed, prepared or committed. *)
        (* The reason we keep this is to make sure we won't contributed on different *)
        (* branches. *Note: this can be violited if Self is evil.* *)
        
        
BlockChain == INSTANCE LocalBlockChain WITH Validator <- Validator,
                                               Self <- Self,
                                               block <- block,
                                               UsedIds <- UsedIds,
                                               block_prepares <- block_prepares,
                                               block_commits <- block_commits
                                               
                                                         
Message ==
  (*************************************************************************)
  
  (* The set of all possible messages.  The ins field indicates the sender. For "propose" *)
  (* message, the "val" field means she propose a block. Since we do not mind the proposed value, we do not *)
  (* record the proposed value here. The "sender" field indicates the sender of a message.   *)
  (*************************************************************************)
  [type : {"propose", "prepare", "commit"}, val : BlockChain!Block, sender : Validator] 
  

Network == INSTANCE Network WITH Message <- Message, endpoint <-Validator,
                                    trans_buffer <- trans_buffer,
                                    recv_buffer <- recv_buffer

-----------------------------------------------------------------------------
PVTypeOK == /\ Network!NetworkTypeOK
             /\ \A n \in Validator : BlockChain!BCTypeOK
             /\ status \in {"working", "prepared", "committed", "finality"}
             
PVInit == /\ Network!NetworkInit 
           /\ \A n \in Validator: BlockChain!BCInit
           /\ status = "working"
           
PVPeriodInit == /\ status' = "working"
(**This is for init at the begining of each period   *)

------------------------------------------------------------------------------
(* Status checking functions *)
IsImpossibleToReachCommitStatus == 0 \* todo
(* This means there are two blocks, a and b, neither of them can get more the 2/3 prepares *)
(* or commit. *)

AlreadyReachFinalityStatus == 0 \* todo
(* The Self status already reach finality. *)


------------------------------------------------------------------------------
(* network message handler  *)
PVProposeBlock == LET tail == IF contributed_block # {} 
                              THEN BlockChain!TailBlock[CHOOSE v : v \in contributed_block]
                              ELSE CHOOSE v : v \in BlockChain!AllTails
                  IN LET b == BlockChain!BCGenBlockWithTail(tail)
                     IN /\ BlockChain!BCAddBlock(b)
                        /\ Network!Broadcast(Self, [type |-> "propose", val |-> b, sender |-> Self])
                        /\ status = "working"
                        /\ status' = "prepared"
                        /\ UsedIds' = UsedIds \cup {b.id}
                        /\ contributed_block' = contributed_block \cup {b}
                        /\ BlockChain!BCPrepareBlock(b, Self)
                       

PVHandleProposeMsg(v) == /\ v.type = "propose"
                         /\ status = "working"
                         /\ status' = "prepared"
                         /\ contributed_block' = contributed_block \cup {v.val}
                         /\ BlockChain!BCAddBlock(v.val)
                         /\ Network!Broadcast(Self, [type |-> "prepare", val |-> v.val, sender |-> Self])
                         /\ BlockChain!BCPrepareBlock(v.val, Self)
                         
PVHandlePrepareMsg(v) ==  /\ v.type = "prepare"
                          /\  \/ /\ status = "working"
                                 /\ status' = "prepared"
                                 /\ contributed_block' = contributed_block \cup {v.val}
                                 /\ BlockChain!BCAddBlock(v.val)
                                 /\ Network!Broadcast(Self, [type |-> "prepare", val |-> v.val, sender |-> Self])
                                 /\ BlockChain!BCPrepareBlock(v.val, Self)
                              \/ /\ status \in {"prepared", "committed", "finality"}
                                 /\ BlockChain!BCAddBlock(v.val)
                                 /\ BlockChain!BCPrepareBlock(v.val, Self)
                                 
PVHandleCommitMsg(v) == /\ v.type = "commit"
                        /\  \/ /\ status = "prepared"
                         
PVHandleRecvMsg(v) == \/ PVHandleProposeMsg(v)
                      \/ PVHandlePrepareMsg(v)
                      \/ PVHandleCommitMsg(v)
                      
-----------------------------------------------------------------------------
(* Some action for local block chain. This can be one of the following actions: *)
(*     1. choose some block to prepare    *)
(*     2. choose some block to commit     *)
(*     3. choose some block to remove, this is because the node finds some inconsistency *)
(* and the node wants make it consistency for maximum benifits.        *) 
(*     4. change block status if some block becomes final. This should be optional.     *)

PVChooseToPrepare == 0 \* todo
PVChooseToCommit == 0 \* todo
PVChooseToRemoveBlocks == 0 \* todo
PVChooseToChangeBlockStatus == 0 \* todo

PVChooseAction == \/ PVChooseToPrepare
                  \/ PVChooseToCommit
                  \/ PVChooseToRemoveBlocks
                  \/ PVChooseToChangeBlockStatus
-----------------------------------------------------------------------------

(* Here for the next steps, we don't do PVProposeBlock because we wanna leave *)
(* this action to PoD, and PoD will decide which Validator to propose. *)
PVNext == \/ \E msg \in Network!RecvedMsgs(Self): 
               /\ PVHandleRecvMsg(msg)
               /\ Network!RemoveMsg(Self, msg)
          \/ PVChooseAction
            

-----------------------------------------------------------------------------

PVConsistency == BlockChain!BCConsistency

=============================================================================
\* Modification History
\* Last modified Sat Feb 03 19:35:16 CST 2018 by xuepeng
\* Created Sat Feb 03 15:40:11 CST 2018 by xuepeng
