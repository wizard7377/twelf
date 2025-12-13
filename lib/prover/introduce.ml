(* Introduce *)
(* Author: Carsten Schuermann *)

functor (* GEN BEGIN FUNCTOR DECL *) Introduce
  ((*! structure IntSyn' : INTSYN !*)
   (*! structure Tomega' : TOMEGA !*)
   (*! sharing Tomega'.IntSyn = IntSyn' !*)
   structure State' : STATE
   structure TomegaNames : TOMEGANAMES
   (*! sharing State'.IntSyn = IntSyn' !*)
   (*! sharing State'.Tomega = Tomega' !*)
       ) : INTRODUCE  =
struct
  (*! structure IntSyn = IntSyn' !*)
  (*! structure Tomega = Tomega' !*)
  structure State = State'

  local
  structure S = State'
  structure T = Tomega
  structure I = IntSyn

    exception Error = S.Error
    type operator = T.prg * T.prg

(*    fun stripTC (T.Abs (_, TC)) = TC *)
      fun stripTC TC = TC


    fun (* GEN BEGIN FUN FIRST *) stripTCOpt NONE = NONE (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) stripTCOpt (SOME TC) = SOME (stripTC TC) (* GEN END FUN BRANCH *)

    fun (* GEN BEGIN FUN FIRST *) stripDec (T.UDec D) = T.UDec D (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) stripDec (T.PDec (name, F, TC1, TC2)) = T.PDec (name, F, TC1, stripTCOpt TC2) (* GEN END FUN BRANCH *)

    fun (* GEN BEGIN FUN FIRST *) strip I.Null = I.Null (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) strip (I.Decl (Psi, D)) = I.Decl (strip Psi, stripDec D) (* GEN END FUN BRANCH *)


    (* expand S = S'

       Invariant:
       If   S = (Psi |> all x1:A1 .... xn: An. F)
       and  F does not start with an all quantifier
       then S' = (Psi, x1:A1, ... xn:An |> F)
    *)
    fun (* GEN BEGIN FUN FIRST *) expand (S.Focus (R as T.EVar (Psi, r, T.All ((D, _), F), NONE, NONE, _), W)) =
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val D' = TomegaNames.decName (Psi, D) (* GEN END TAG OUTSIDE LET *)
        in
          SOME (R, T.Lam (D', T.newEVar (I.Decl (strip Psi, D'), F)))
        end (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) expand (S.Focus (R as T.EVar (Psi, r, T.Ex ((D as I.Dec (_, V), _), F), NONE, NONE, _), W)) =
           let
             (* GEN BEGIN TAG OUTSIDE LET *) val X = I.newEVar (T.coerceCtx (Psi), V) (* GEN END TAG OUTSIDE LET *)
             (* GEN BEGIN TAG OUTSIDE LET *) val Y = T.newEVar (Psi, T.forSub (F, T.Dot (T.Exp X, T.id))) (* GEN END TAG OUTSIDE LET *)
           in
             SOME (R, T.PairExp (X, Y))
           end (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) expand (S.Focus (R as T.EVar (Psi, r, T.True, NONE, NONE, _), W)) =
           (SOME (R, T.Unit)) (* GEN END FUN BRANCH *)

      | (* GEN BEGIN FUN BRANCH *) expand (S.Focus (T.EVar (Psi, r, T.FClo (F, s), TC1, TC2, X), W)) =
           expand (S.Focus (T.EVar (Psi, r, T.forSub (F, s), TC1, TC2, X), W)) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) expand (S.Focus (T.EVar (Psi, r, _, _, _, _), W)) = NONE (* GEN END FUN BRANCH *)

    (* apply O = S

       Invariant:
       O = S
    *)
    fun apply (T.EVar (_, r, _, _, _, _), P) = (r := SOME P)   (* need to trail for back *)

    (* menu O = s

       Invariant:
       s = "Apply universal introduction rules"
    *)
    fun menu (r, P) = "Intro " ^ TomegaPrint.nameEVar r


  in
    exception Error = Error
    type operator = operator

    (* GEN BEGIN TAG OUTSIDE LET *) val expand = expand (* GEN END TAG OUTSIDE LET *)
    (* GEN BEGIN TAG OUTSIDE LET *) val apply = apply (* GEN END TAG OUTSIDE LET *)
    (* GEN BEGIN TAG OUTSIDE LET *) val menu =menu (* GEN END TAG OUTSIDE LET *)
  end
end (* GEN END FUNCTOR DECL *)