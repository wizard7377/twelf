(* module ModeSyn  in modesyn.sml *)

module ModeTable =
  ModeTable (module Table = IntRedBlackTree);

module ModeDec =
  ModeDec ((*! module ModeSyn' = ModeSyn !*)
	   (*! module Paths' = Paths !*)
	     );

module ModeCheck =
  ModeCheck ((*! module IntSyn = IntSyn !*)
	     module ModeTable = ModeTable
             module Whnf = Whnf
	     module Index = Index
	     (*! module Paths = Paths !*)
	     module Origins = Origins);

module ModePrint =
  ModePrint ((*! module ModeSyn' = ModeSyn !*)
	     module Names = Names
	     module Formatter = Formatter
	     module Print = Print);
