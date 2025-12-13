(* Weakening substitutions *)
(* Author: Carsten Schuermann *)

functor (* GEN BEGIN FUNCTOR DECL *) Weaken ((*! structure IntSyn' : INTSYN !*)
                structure Whnf : WHNF
                (*! sharing Whnf.IntSyn = IntSyn' !*)
                  ) : WEAKEN =
struct
  (*! structure IntSyn = IntSyn' !*)

  local
    structure I = IntSyn

    (* strengthenExp (U, s) = U'

       Invariant:
       If   G |- s : G'
       and  G |- U : V
       then G' |- U' = U[s^-1] : V [s^-1]
    *)
    fun strengthenExp (U, s) = Whnf.normalize (Whnf.cloInv (U, s), I.id)

    (* strengthenDec (x:V, s) = x:V'

       Invariant:
       If   G |- s : G'
       and  G |- V : L
       then G' |- V' = V[s^-1] : L
    *)
    fun strengthenDec (I.Dec (name, V), s) = I.Dec (name, strengthenExp (V, s))

    (* strengthenCtx (G, s) = (G', s')

       If   G0 |- G ctx
       and  G0 |- s G1
       then G1 |- G' = G[s^-1] ctx
       and  G0 |- s' : G1, G'
    *)
    fun (* GEN BEGIN FUN FIRST *) strengthenCtx (I.Null, s) = (I.Null, s) (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) strengthenCtx (I.Decl (G, D), s) =
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val (G', s') = strengthenCtx (G, s) (* GEN END TAG OUTSIDE LET *)
        in
          (I.Decl (G', strengthenDec (D, s')), I.dot1 s')
        end (* GEN END FUN BRANCH *)

    fun strengthenSub (s, t) = Whnf.compInv (s, t)

    fun (* GEN BEGIN FUN FIRST *) strengthenSpine (I.Nil, t) = I.Nil (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) strengthenSpine (I.App (U, S), t) = I.App (strengthenExp (U, t), strengthenSpine (S, t)) (* GEN END FUN BRANCH *)

  in
    (* GEN BEGIN TAG OUTSIDE LET *) val strengthenExp = strengthenExp (* GEN END TAG OUTSIDE LET *)
    (* GEN BEGIN TAG OUTSIDE LET *) val strengthenSpine = strengthenSpine (* GEN END TAG OUTSIDE LET *)
    (* GEN BEGIN TAG OUTSIDE LET *) val strengthenDec = strengthenDec (* GEN END TAG OUTSIDE LET *)
    (* GEN BEGIN TAG OUTSIDE LET *) val strengthenCtx = strengthenCtx (* GEN END TAG OUTSIDE LET *)
    (* GEN BEGIN TAG OUTSIDE LET *) val strengthenSub = strengthenSub (* GEN END TAG OUTSIDE LET *)
  end
end (* GEN END FUNCTOR DECL *) (* functor Weaken *)
