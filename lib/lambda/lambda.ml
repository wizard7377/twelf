(** Lambda Calculus and Internal Syntax Module.

    This module aggregates the core lambda calculus functionality for the LF logical
    framework, including:

    - Internal syntax representation (terms, types, contexts)
    - Weak head normal form computation
    - Unification with and without trailing
    - Term normalization and conversion
    - Pattern matching
    - Abstract operations
    - Constraint solving

    This is one of the foundational modules of the Twelf implementation, providing
    the core data structures and operations for representing and manipulating LF terms.

    @see <http://twelf.org> Twelf Project Homepage
*)

open Basis ;;
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

structure Tomega : Tomega.TOMEGA =
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

(* structure Normalize : Normalize.Normalize.NORMALIZE =  
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
