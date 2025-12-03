module TabledSyn = 
  TabledSyn ((*! module IntSyn' = IntSyn !*)
	   module Names = Names
	   module Table = IntRedBlackTree
	   module Index = Index);
