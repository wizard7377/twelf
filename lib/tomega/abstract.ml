(* Converter from relational representation to a functional
   representation of proof terms *)
(* Author: Carsten Schuermann *)

functor (* GEN BEGIN FUNCTOR DECL *) TomegaAbstract
  (structure Global : GLOBAL
   structure Abstract : ABSTRACT
   structure Whnf : WHNF
   structure Subordinate : SUBORDINATE)
     : TOMEGAABSTRACT =
struct

  exception Error of string


  local
    structure T = Tomega
    structure I = IntSyn
    structure M = ModeSyn
    structure S = Subordinate
    structure A = Abstract






    fun (* GEN BEGIN FUN FIRST *) shiftCtx (I.Null, t) = (I.Null, t) (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) shiftCtx (I.Decl (G, D), t) =
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val (G', t') =  shiftCtx (G, t) (* GEN END TAG OUTSIDE LET *)
        in
          (I.Decl (G', I.decSub (D, t')), I.dot1 t')
        end (* GEN END FUN BRANCH *)

    (* dotn (t, n) = t'

       Invariant:
       If   Psi0 |- t : Psi
       and  |G| = n   for any G
       then Psi0, G[t] |- t : Psi, G
    *)
    fun (* GEN BEGIN FUN FIRST *) dotn (t, 0) = t (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) dotn (t, n) = I.dot1 (dotn (t, n-1)) (* GEN END FUN BRANCH *)


    fun (* GEN BEGIN FUN FIRST *) strengthenToSpine (I.Shift _ (* =0 *), 0, (n, S)) = S (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) strengthenToSpine (I.Dot (I.Idx _ (* = 1 *), t), l, (n, S)) =
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val t' = I.comp (t, I.invShift) (* GEN END TAG OUTSIDE LET *)
        in
          strengthenToSpine (t', l-1, (n+1, I.App (I.Root (I.BVar n, I.Nil), S)))
        end (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) strengthenToSpine (I.Dot (I.Undef, t), l, (n, S)) =
          strengthenToSpine (t, l-1, (n+1, S)) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) strengthenToSpine (I.Shift k, l, (n, S)) =
          strengthenToSpine (I.Dot (I.Idx (k+1), I.Shift (k+1)), l, (n, S)) (* GEN END FUN BRANCH *)



    (* raiseFor (B, (F, t)) = (P', F'))

       Invariant:
       If   Psi, B, G |-  F for
       and  Psi, G', B' |- t : Psi, B, G
       then Psi, G' |-  F' for
       and  F' = raise (B', F[t])   (using subordination)
    *)
    fun (* GEN BEGIN FUN FIRST *) raiseFor (B', (T.True, t)) = T.True (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) raiseFor (B', (T.And (F1, F2), t)) =
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val F1' = raiseFor (B', (F1, t)) (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val F2' = raiseFor (B', (F2, t)) (* GEN END TAG OUTSIDE LET *)
        in
          T.And (F1', F2')
        end (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) raiseFor (B', (T.Ex ((I.Dec (x, V), Q), F), t)) =
                                                    (* Psi, G', B' |- V[t] : type *)
                                                    (* Psi, B, G, x:V |- F for *)
                                                    (* Psi, G' |- B' ctx  *)
        let
      (*        val (w, S) = subweaken (B', 1, I.targetFam V, I.Nil)     *)
          (* GEN BEGIN TAG OUTSIDE LET *) val w = S.weaken (B', I.targetFam V) (* GEN END TAG OUTSIDE LET *)
                                                   (* B'  |- w  : B''    *)
          (* GEN BEGIN TAG OUTSIDE LET *) val iw = Whnf.invert w (* GEN END TAG OUTSIDE LET *)                    (* B'' |- iw : B'     *)
          (* GEN BEGIN TAG OUTSIDE LET *) val B'' = Whnf.strengthen (iw, B') (* GEN END TAG OUTSIDE LET *)        (* Psi0, G' |- B'' ctx *)
      
          (* GEN BEGIN TAG OUTSIDE LET *) val V' = A.raiseType (B'', I.EClo (V, I.comp (t, iw))) (* GEN END TAG OUTSIDE LET *) (* Psi0, G' |- V' : type *)
      
      
          (* GEN BEGIN TAG OUTSIDE LET *) val (B''', _) = shiftCtx (B', I.shift) (* GEN END TAG OUTSIDE LET *)
                                                    (* Psi, G', x: V' |- B''' ctx *)
      
          (* GEN BEGIN TAG OUTSIDE LET *) val t'' = dotn (I.shift, I.ctxLength B') (* GEN END TAG OUTSIDE LET *)
                                                    (* Psi, G', x: V', B''' |- t'' :   Psi, G', B' *)
                                                    (* Psi, G', B' |- t : Psi, B, G  *)
          (* GEN BEGIN TAG OUTSIDE LET *) val t' = I.comp (t, t'') (* GEN END TAG OUTSIDE LET *)
                                                    (* Psi, G', x:V', B''' |- t' : Psi, B, G *)
      
                                                    (* Psi, G', x:V', B''' |- w : Psi,G', x:V', B'''' *)
          (* GEN BEGIN TAG OUTSIDE LET *) val S = strengthenToSpine (iw, I.ctxLength B', (1, I.Nil)) (* GEN END TAG OUTSIDE LET *)
                                                    (* Psi, G', x:V', B''' |- S : V' [^|B'''|] >> type  *)
          (* GEN BEGIN TAG OUTSIDE LET *) val U = I.Root (I.BVar (I.ctxLength B''' + 1), S) (* GEN END TAG OUTSIDE LET *)
                                                    (* Psi, G', x:V', B''' |- U : V[t'] *)
      
          (* GEN BEGIN TAG OUTSIDE LET *) val t''' = Whnf.dotEta (I.Exp U, t') (* GEN END TAG OUTSIDE LET *)            (* Psi, G', x:V', B''' |- t''' :  Psi, B, G, x:V *)
          (* GEN BEGIN TAG OUTSIDE LET *) val F' = raiseFor (B''', (F, t''')) (* GEN END TAG OUTSIDE LET *)       (* Psi, G', x:V' |- F' for*)
        in
          T.Ex ((I.Dec (x, V'), Q), F')(* Psi, G', x:V', B''' |- t''' :  Psi, B, G, x:V *)
        end (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) raiseFor (_, (T.All _, _)) = raise Domain (* GEN END FUN BRANCH *)


    (* raisePrg (G, P, F) = (P', F'))

       Invariant:
       If   Psi, G |- P in F
       and  Psi |- G : blockctx
       then Psi |- P' in F'
       and  P = raise (G, P')   (using subordination)
       and  F = raise (G, F')   (using subordination)
    *)
    fun (* GEN BEGIN FUN FIRST *) raisePrg (G, (T.Unit, t), _) = T.Unit (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) raisePrg (G, (T.PairPrg (P1, P2), t), T.And (F1, F2)) =
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val P1' = raisePrg (G, (P1, t), F1) (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val P2' = raisePrg (G, (P2, t), F2) (* GEN END TAG OUTSIDE LET *)
        in
          T.PairPrg (P1', P2')
        end (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) raisePrg (G, (T.PairExp (U, P), t), T.Ex ((I.Dec (_, V), _), F)) =
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val w = S.weaken (G, I.targetFam V) (* GEN END TAG OUTSIDE LET *)
                                                   (* G  |- w  : G'    *)
          (* GEN BEGIN TAG OUTSIDE LET *) val iw = Whnf.invert w (* GEN END TAG OUTSIDE LET *)                    (* G' |- iw : G     *)
          (* GEN BEGIN TAG OUTSIDE LET *) val G' = Whnf.strengthen (iw, G) (* GEN END TAG OUTSIDE LET *)        (* Psi0, G' |- B'' ctx *)
      
          (* GEN BEGIN TAG OUTSIDE LET *) val U' = A.raiseTerm (G', I.EClo (U, I.comp (t, iw))) (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val P' = raisePrg (G, (P, t), F) (* GEN END TAG OUTSIDE LET *)
        in
          T.PairExp (U', P')
        end (* GEN END FUN BRANCH *)


    fun raiseP (G, P, F) =
      let
        (* GEN BEGIN TAG OUTSIDE LET *) val (G', s) = T.deblockify G (* GEN END TAG OUTSIDE LET *)
    (*      val P' = T.normalizePrg (P, s) (* G' |- P' : F' *) *)
        (* GEN BEGIN TAG OUTSIDE LET *) val F' = T.forSub (F, s) (* GEN END TAG OUTSIDE LET *)
        (* GEN BEGIN TAG OUTSIDE LET *) val P'' = raisePrg (G', (P, T.coerceSub s), F') (* GEN END TAG OUTSIDE LET *)
      in
        P''
      end

    fun raiseF (G, (F, t)) =
      let
        (* GEN BEGIN TAG OUTSIDE LET *) val (G', s) = T.deblockify G (* GEN END TAG OUTSIDE LET *)
        (* GEN BEGIN TAG OUTSIDE LET *) val F' = raiseFor (G', (F, I.comp (t, T.coerceSub s))) (* GEN END TAG OUTSIDE LET *)
      in
        F'
      end



  in
    (* GEN BEGIN TAG OUTSIDE LET *) val raisePrg = (* GEN BEGIN FUNCTION EXPRESSION *) fn (G, P, F) => raisePrg (G, (P, I.id), F) (* GEN END FUNCTION EXPRESSION *) (* GEN END TAG OUTSIDE LET *)
    (* GEN BEGIN TAG OUTSIDE LET *) val raiseP = raiseP (* GEN END TAG OUTSIDE LET *)
    (* GEN BEGIN TAG OUTSIDE LET *) val raiseFor = raiseFor (* GEN END TAG OUTSIDE LET *)
    (* GEN BEGIN TAG OUTSIDE LET *) val raiseF = raiseF (* GEN END TAG OUTSIDE LET *)
  end
end (* GEN END FUNCTOR DECL *) (* functor TomegaAbstract *)
