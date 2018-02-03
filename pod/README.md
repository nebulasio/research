# Formalized specification of PoD

We use TLA+ to specify PoD. You may find more details about TLA+ here: https://lamport.azurewebsites.net/tla/tla.html


####The structure is as follow:

Network.tla -- defines how network transfer messages;

LocalBlockChain.tla -- defines the basic behavior of a block chain on a single
node;

PODValidator.tla -- defines how a validator performs when recv messages and how
to manipulate local block chain;

POD.tla -- defines the high level behavior of POD, like how to keep the block
chain growing.

####The following files are no used anymore, we just keep them here as comparison:

PODCommit.tla

Please let us know if you have any comment!

