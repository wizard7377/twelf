open Basis ;; 
(* Lemma *)

(* Author: Carsten Schuermann *)

module type LEMMA = sig
  module MetaSyn : Metasyn.METASYN

  exception Error of string

  val apply : MetaSyn.state * IntSyn.cid -> MetaSyn.state
end

(* signature LEMMA *)
(* Lemma *)

(* Author: Carsten Schuermann *)

module Lemma
    (MetaSyn' : Metasyn.METASYN)
    (MetaAbstract : Meta_abstract.METAABSTRACT) : LEMMA = struct
  module MetaSyn = MetaSyn'

  exception Error of string

  module A = MetaAbstract
  module M = MetaSyn
  module I = IntSyn
  (* createEVars (G, M, B) = ((G', M', B'), s')

       Invariant:
       If   |- G ctx
       then |- G' ctx
       and  . |- s' : G
       M and B are mode and bound contexts matching G, and similarly for_sml M' and B'.
    *)

  let rec createEVars = function
    | M.Prefix (I.Null, I.Null, I.Null) ->
        (M.Prefix (I.Null, I.Null, I.Null), I.id)
    | M.Prefix (I.Decl (G, D), I.Decl (M, M.Top), I.Decl (B, b)) ->
        let M.Prefix (G', M', B'), s' = createEVars (M.Prefix (G, M, B)) in
        ( M.Prefix
            (I.Decl (G', I.decSub (D, s')), I.Decl (M', M.Top), I.Decl (B', b)),
          I.dot1 s' )
    | M.Prefix (I.Decl (G, I.Dec (_, V)), I.Decl (M, M.Bot), I.Decl (B, _)) ->
        let M.Prefix (G', M', B'), s' = createEVars (M.Prefix (G, M, B)) in
        let X = I.newEVar (G', I.EClo (V, s')) in
        (M.Prefix (G', M', B'), I.Dot (I.Exp X, s'))
  (* apply (((G, M), V), a) = ((G', M'), V')

       Invariant:
       If   |- G ctx
       and  G |- M mtx
       and  a is a type constant of type Va: Sigma (a) = Va
       then |- G' ctx
       and  G' |- M' mtx
       and  G' |- S' : Va > type
       and  G' |- s' : G
       and  G' |- V' = {a S'}. V[s' o ^]
       and  ((G', M'), V') is a state
    *)

  let rec apply (M.State (name, GM, V), a) =
    (* Vs' = type *)
    let GM', s' = createEVars GM in
    let U', Vs' = M.createAtomConst (G', I.Const a) in
    A.abstract
      (M.State
         ( name,
           GM',
           I.Pi ((I.Dec (None, U'), I.No), I.EClo (V, I.comp (s', I.shift))) ))

  let apply = apply
  (* local *)
end

(* functor lemma *)
