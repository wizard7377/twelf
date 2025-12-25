open Basis ;; 
(* Unification on Formulas *)

(* Author: Carsten Schuermann *)

module type TOMEGAUNIFY = sig
  (*! structure IntSyn : Intsyn.INTSYN !*)
  (*! structure Tomega : Tomega.TOMEGA !*)
  exception Unify of string

  val unifyFor : Tomega.dec IntSyn.ctx * Tomega.for_sml * Tomega.for_sml -> unit
end

(* Signature Tomega.Typecheck.TOMEGATYPECHECK *)
(* Unification on Formulas *)

(* Author: Carsten Schuermann *)

module TomegaUnify
    (Abstract : Abstract.ABSTRACT)
    (TypeCheck : Typecheck.TYPECHECK)
    (Conv : Conv.CONV)
    (Normalize : Normalize.Normalize.NORMALIZE)
    (Whnf : Whnf.WHNF)
    (Print : Print.PRINT)
    (TomegaPrint : Tomega.Tomegaprint.TOMEGAPRINT)
    (Subordinate : Subordinate.SUBORDINATE)
    (Weaken : Weaken.Weaken.WEAKEN) : Tomega.TOMEGAUNIFY = struct
  (*! structure IntSyn = IntSyn' !*)

  (*! structure Tomega = Tomega' !*)

  exception Unify of string

  module I = IntSyn
  module T = Tomega
  (* unifyFor (Psi, F1, F2) = R

       Invariant:
       If   F1, F2 contain free variables X1 ... Xn
       and  Psi |- F1 for_sml
       and  Psi |- F2 for_sml
       and  there exists an instantiation I for_sml X1 ...Xn such that
       and  Psi[I] |- F1[I] = F2[I]
       then R = ()
       otherwise exception Unify is raised
    *)

  let rec unifyFor (Psi, F1, F2) =
    unifyForN (Psi, T.forSub (F1, T.id), T.forSub (F2, T.id))

  and unifyForN = function
    | Psi, T.True, T.True -> ()
    | Psi, T.Ex ((D1, _), F1), T.Ex ((D2, _), F2) ->
        unifyDec (Psi, T.UDec D1, T.UDec D2);
        unifyFor (I.Decl (Psi, T.UDec D1), F1, F2)
    | Psi, T.All ((D1, _), F1), T.All ((D2, _), F2) ->
        unifyDec (Psi, D1, D2);
        unifyFor (I.Decl (Psi, D1), F1, F2)
    | Psi, T.FVar (_, r), F -> r := Some F
    | Psi, F, T.FVar (_, r) -> r := Some F
    | Psi, _, _ -> raise (Unify "Formula mismatch")

  and unifyDec = function
    | Psi, T.UDec D1, T.UDec D2 ->
        if Conv.convDec ((D1, I.id), (D2, I.id)) then ()
        else raise (Unify "Declaration mismatch")
    | Psi, T.PDec (_, F1), T.PDec (_, F2) -> unifyFor (Psi, F1, F2)

  let unifyFor = unifyFor
end
