(* Lemma *)
(* Author: Carsten Schuermann *)

let recctor Lemma (module MetaSyn' : METASYN
               module MetaAbstract : METAABSTRACT
               sharing MetaAbstract.MetaSyn = MetaSyn')
  : LEMMA =
struct
  module MetaSyn = MetaSyn'

  exception Error of string

  local
    module A = MetaAbstract
    module M = MetaSyn
    module I = IntSyn

    (* createEVars (G, M, B) = ((G', M', B'), s')

       Invariant:
       If   |- G ctx
       then |- G' ctx
       and  . |- s' : G
       M and B are mode and bound contexts matching G, and similarly for M' and B'.
    *)
    fun createEVars (M.Prefix (I.Null, I.Null, I.Null)) =
          (M.Prefix (I.Null, I.Null, I.Null), I.id)
      | createEVars (M.Prefix (I.Decl (G, D), I.Decl (M, M.Top), I.Decl (B, b))) =
        let
          let (M.Prefix (G', M', B'), s') = createEVars (M.Prefix (G, M, B))
        in
          (M.Prefix (I.Decl (G', I.decSub (D, s')), I.Decl (M', M.Top), I.Decl (B', b)),
           I.dot1 s')
        end
      | createEVars (M.Prefix (I.Decl (G, I.Dec (_, V)), I.Decl (M, M.Bot), I.Decl (B, _))) =
        let
          let (M.Prefix (G', M', B'), s') = createEVars (M.Prefix (G, M, B))
          let X  = I.newEVar (G', I.EClo (V, s'))
        in
          (M.Prefix (G', M', B'), I.Dot (I.Exp (X), s'))
        end

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
    fun apply (M.State (name, GM, V), a) =
        let
          let (GM' as M.Prefix (G', M', B'), s') = createEVars GM
          let (U', Vs') = M.createAtomConst (G', I.Const a)  (* Vs' = type *)
        in
          A.abstract (M.State (name, GM', I.Pi ((I.Dec (NONE, U'), I.No),
                                                I.EClo (V, I.comp (s',I.shift)))))
        end

  in
    let apply = apply
  end (* local *)
end; (* functor lemma *)
