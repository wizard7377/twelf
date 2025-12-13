(* Lemma *)
(* Author: Carsten Schuermann *)

functor (* GEN BEGIN FUNCTOR DECL *) Lemma (structure MetaSyn' : METASYN
               structure MetaAbstract : METAABSTRACT
               sharing MetaAbstract.MetaSyn = MetaSyn')
  : LEMMA =
struct
  structure MetaSyn = MetaSyn'

  exception Error of string

  local
    structure A = MetaAbstract
    structure M = MetaSyn
    structure I = IntSyn

    (* createEVars (G, M, B) = ((G', M', B'), s')

       Invariant:
       If   |- G ctx
       then |- G' ctx
       and  . |- s' : G
       M and B are mode and bound contexts matching G, and similarly for M' and B'.
    *)
    fun (* GEN BEGIN FUN FIRST *) createEVars (M.Prefix (I.Null, I.Null, I.Null)) =
          (M.Prefix (I.Null, I.Null, I.Null), I.id) (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) createEVars (M.Prefix (I.Decl (G, D), I.Decl (M, M.Top), I.Decl (B, b))) =
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val (M.Prefix (G', M', B'), s') = createEVars (M.Prefix (G, M, B)) (* GEN END TAG OUTSIDE LET *)
        in
          (M.Prefix (I.Decl (G', I.decSub (D, s')), I.Decl (M', M.Top), I.Decl (B', b)),
           I.dot1 s')
        end (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) createEVars (M.Prefix (I.Decl (G, I.Dec (_, V)), I.Decl (M, M.Bot), I.Decl (B, _))) =
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val (M.Prefix (G', M', B'), s') = createEVars (M.Prefix (G, M, B)) (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val X  = I.newEVar (G', I.EClo (V, s')) (* GEN END TAG OUTSIDE LET *)
        in
          (M.Prefix (G', M', B'), I.Dot (I.Exp (X), s'))
        end (* GEN END FUN BRANCH *)

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
          (* GEN BEGIN TAG OUTSIDE LET *) val (GM' as M.Prefix (G', M', B'), s') = createEVars GM (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val (U', Vs') = M.createAtomConst (G', I.Const a) (* GEN END TAG OUTSIDE LET *)  (* Vs' = type *)
        in
          A.abstract (M.State (name, GM', I.Pi ((I.Dec (NONE, U'), I.No),
                                                I.EClo (V, I.comp (s',I.shift)))))
        end

  in
    (* GEN BEGIN TAG OUTSIDE LET *) val apply = apply (* GEN END TAG OUTSIDE LET *)
  end (* local *)
end (* GEN END FUNCTOR DECL *); (* functor lemma *)
