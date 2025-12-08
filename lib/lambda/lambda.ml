(* Now in intsyn.fun *)
(*
module IntSyn =
  IntSyn (module Global = Global);
*)

(* Now in tomega.sml *)
(*
module Whnf =
  Whnf ((*! module IntSyn' = IntSyn !*));

module Conv =
  Conv ((*! module IntSyn' = IntSyn !*)
	module Whnf = Whnf);

(Tomega : TOMEG)A =
   Tomega (module IntSyn' = IntSyn
	   module Whnf = Whnf
	   module Conv = Conv)
*)

module Constraints =
  Constraints ((*! module IntSyn' = IntSyn !*)
	       module Conv = Conv);

module UnifyNoTrail =
  Unify ((*! module IntSyn' = IntSyn !*)
	 module Whnf = Whnf
	 module Trail = NoTrail);

module UnifyTrail =
  Unify ((*! module IntSyn' = IntSyn !*)
	 module Whnf = Whnf
	 module Trail = Trail);

(* (Normalize : NORMALIZ)E =  
  Normalize ((*! module IntSyn' = IntSyn !*)
             (*! module Tomega' = Tomega !*)
             module Whnf = Whnf)
 *)

module Match = 
  Match (module Whnf = Whnf
	 module Unify = UnifyTrail
	 module Trail = Trail);

module Abstract =
  Abstract (module Whnf = Whnf
	    module Constraints = Constraints
	    module Unify = UnifyNoTrail);

module Approx =
  Approx ((*! module IntSyn' = IntSyn !*)
          module Whnf = Whnf);
