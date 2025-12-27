open Basis

(* Manipulating Constraints *)

(* Author: Jeff Polakow, Frank Pfenning *)

(* Modified: Roberto Virga *)

module type CONSTRAINTS = sig
  (*! structure IntSyn : Intsyn.INTSYN !*)
  exception Error of IntSyn.cnstr list

  val simplify : IntSyn.cnstr list -> IntSyn.cnstr list
  val warnConstraints : string list -> unit
end

(* signature CONSTRAINTS *)
(* Manipulating Constraints *)

(* Author: Jeff Polakow, Frank Pfenning *)

(* Modified: Roberto Virga *)

module Constraints (Conv : Conv.CONV) : CONSTRAINTS = struct
  (*! structure IntSyn = IntSyn' !*)

  exception Error of IntSyn.cnstr list
  (*
     Constraints cnstr are of the form (X<I>[s] = U).
     Invariants:
       G |- s : G'  G' |- X<I> : V
       G |- U : W
       G |- V[s] == W : L
       (X<>,s) is whnf, but X<>[s] is not a pattern
     If X<I> is uninstantiated, the constraint is inactive.
     If X<I> is instantiated, the constraint is active.

     Constraints are attached directly to the EVar X
     or to a descendent  -fp?
  *)

  module I = IntSyn
  (* simplify cnstrs = cnstrs'
       Effects: simplifies the constraints in cnstrs by removing constraints
         of the form U = U' where G |- U == U' : V (mod beta/eta)
         Neither U nor U' needs to be a pattern
         *)

  let rec simplify = function
    | [] -> []
    | { contents = I.Solved } :: cnstrs -> simplify cnstrs
    | Eqn :: cnstrs ->
        if Conv.conv ((U1, I.id), (U2, I.id)) then simplify cnstrs
        else Eqn :: simplify cnstrs
    | FgnCnstr :: cnstrs ->
        if I.FgnCnstrStd.Simplify.apply csfc () then simplify cnstrs
        else FgnCnstr :: simplify cnstrs

  let rec namesToString = function
    | name :: [] -> name ^ "."
    | name :: names -> name ^ ", " ^ namesToString names

  let rec warnConstraints = function
    | [] -> ()
    | names -> print ("Constraints remain on " ^ namesToString names ^ "\n")

  let simplify = simplify
  let namesToString = namesToString
  let warnConstraints = warnConstraints
end

(* functor Constraints *)
