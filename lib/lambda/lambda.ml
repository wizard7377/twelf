(* Now in intsyn.fun *)

(*
structure IntSyn =
  IntSyn (structure Global = Global);
*)

(* Now in tomega.sml *)

(*
structure Whnf =
  Whnf ((*! structure IntSyn' = IntSyn !*));

structure Conv =
  Conv ((*! structure IntSyn' = IntSyn !*)
	structure Whnf = Whnf);

structure Tomega : TOMEGA =
   Tomega (structure IntSyn' = IntSyn
	   structure Whnf = Whnf
	   structure Conv = Conv)
*)

module Constraints = Constraints (struct
  module Conv = Conv
end)

module UnifyNoTrail =
  Unify
    (struct
      module Whnf = Whnf
    end)
    (struct
      module Trail = NoTrail
    end)

module UnifyTrail =
  Unify
    (struct
      module Whnf = Whnf
    end)
    (struct
      module Trail = Trail
    end)

(* structure Normalize : NORMALIZE =  
  Normalize ((*! structure IntSyn' = IntSyn !*)
             (*! structure Tomega' = Tomega !*)
             structure Whnf = Whnf)
 *)

module Match =
  Match
    (struct
      module Whnf = Whnf
    end)
    (struct
      module Unify = UnifyTrail
    end)
    (struct
      module Trail = Trail
    end)

module Abstract =
  Abstract
    (struct
      module Whnf = Whnf
    end)
    (struct
      module Constraints = Constraints
    end)
    (struct
      module Unify = UnifyNoTrail
    end)

module Approx = Approx (struct
  module Whnf = Whnf
end)
