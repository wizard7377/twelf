(* Converter from relational representation to a functional
   representation of proof terms *)
(* Author: Carsten Schuermann *)

module TomegaAbstract
  (Global : GLOBAL)
   (Abstract : ABSTRACT)
   (Whnf : WHNF)
   (Subordinate : SUBORDINATE)
     : TOMEGAABSTRACT =
struct

  exception Error of string


  local
    module T = Tomega
    module I = IntSyn
    module M = ModeSyn
    module S = Subordinate
    module A = Abstract






    let rec shiftCtx = function (I.Null, t) -> (I.Null, t)
      | (I.Decl (G, D), t) -> 
        let
          let (G', t') =  shiftCtx (G, t)
        in
          (I.Decl (G', I.decSub (D, t')), I.dot1 t')
        end

    (* dotn (t, n) = t'

       Invariant:
       If   Psi0 |- t : Psi
       and  |G| = n   for any G
       then Psi0, G[t] |- t : Psi, G
    *)
    let rec dotn = function (t, 0) -> t
      | (t, n) -> I.dot1 (dotn (t, n-1))


    let rec strengthenToSpine = function (I.Shift _ (* -> 0 *), 0, (n, S)) = S
      | (I.Dot (I.Idx _ (* -> 1 *), t), l, (n, S)) =
        let
          let t' = I.comp (t, I.invShift)
        in
          strengthenToSpine (t', l-1, (n+1, I.App (I.Root (I.BVar n, I.Nil), S)))
        end
      | (I.Dot (I.Undef, t), l, (n, S)) -> 
          strengthenToSpine (t, l-1, (n+1, S))
      | (I.Shift k, l, (n, S)) -> 
          strengthenToSpine (I.Dot (I.Idx (k+1), I.Shift (k+1)), l, (n, S))



    (* raiseFor (B, (F, t)) = (P', F'))

       Invariant:
       If   Psi, B, G |-  F for
       and  Psi, G', B' |- t : Psi, B, G
       then Psi, G' |-  F' for
       and  F' = raise (B', F[t])   (using subordination)
    *)
    let rec raiseFor = function (B', (T.True, t)) -> T.True
      | (B', (T.And (F1, F2), t)) -> 
        let
          let F1' = raiseFor (B', (F1, t))
          let F2' = raiseFor (B', (F2, t))
        in
          T.And (F1', F2')
        end
      | (B', (T.Ex ((I.Dec (x, V), Q), F), t)) -> 
                                                    (* Psi, G', B' |- V[t] : type *)
                                                    (* Psi, B, G, x:V |- F for *)
                                                    (* Psi, G' |- B' ctx  *)
        let
(*        let (w, S) = subweaken (B', 1, I.targetFam V, I.Nil)     *)
          let w = S.weaken (B', I.targetFam V)
                                                   (* B'  |- w  : B''    *)
          let iw = Whnf.invert w                    (* B'' |- iw : B'     *)
          let B'' = Whnf.strengthen (iw, B')        (* Psi0, G' |- B'' ctx *)

          let V' = A.raiseType (B'', I.EClo (V, I.comp (t, iw))) (* Psi0, G' |- V' : type *)


          let (B''', _) = shiftCtx (B', I.shift)
                                                    (* Psi, G', x: V' |- B''' ctx *)

          let t'' = dotn (I.shift, I.ctxLength B')
                                                    (* Psi, G', x: V', B''' |- t'' :   Psi, G', B' *)
                                                    (* Psi, G', B' |- t : Psi, B, G  *)
          let t' = I.comp (t, t'')
                                                    (* Psi, G', x:V', B''' |- t' : Psi, B, G *)

                                                    (* Psi, G', x:V', B''' |- w : Psi,G', x:V', B'''' *)
          let S = strengthenToSpine (iw, I.ctxLength B', (1, I.Nil))
                                                    (* Psi, G', x:V', B''' |- S : V' [^|B'''|] >> type  *)
          let U = I.Root (I.BVar (I.ctxLength B''' + 1), S)
                                                    (* Psi, G', x:V', B''' |- U : V[t'] *)

          let t''' = Whnf.dotEta (I.Exp U, t')            (* Psi, G', x:V', B''' |- t''' :  Psi, B, G, x:V *)
          let F' = raiseFor (B''', (F, t'''))       (* Psi, G', x:V' |- F' for*)
        in
          T.Ex ((I.Dec (x, V'), Q), F')(* Psi, G', x:V', B''' |- t''' :  Psi, B, G, x:V *)
        end
      | raiseFor (_, (T.All _, _)) = raise Domain


    (* raisePrg (G, P, F) = (P', F'))

       Invariant:
       If   Psi, G |- P in F
       and  Psi |- G : blockctx
       then Psi |- P' in F'
       and  P = raise (G, P')   (using subordination)
       and  F = raise (G, F')   (using subordination)
    *)
    let rec raisePrg = function (G, (T.Unit, t), _) -> T.Unit
      | (G, (T.PairPrg (P1, P2), t), T.And (F1, F2)) -> 
        let
          let P1' = raisePrg (G, (P1, t), F1)
          let P2' = raisePrg (G, (P2, t), F2)
        in
          T.PairPrg (P1', P2')
        end
      | (G, (T.PairExp (U, P), t), T.Ex ((I.Dec (_, V), _), F)) -> 
        let
          let w = S.weaken (G, I.targetFam V)
                                                   (* G  |- w  : G'    *)
          let iw = Whnf.invert w                    (* G' |- iw : G     *)
          let G' = Whnf.strengthen (iw, G)        (* Psi0, G' |- B'' ctx *)

          let U' = A.raiseTerm (G', I.EClo (U, I.comp (t, iw)))
          let P' = raisePrg (G, (P, t), F)
        in
          T.PairExp (U', P')
        end


    let rec raiseP (G, P, F) =
      let
        let (G', s) = T.deblockify G
(*      let P' = T.normalizePrg (P, s) (* G' |- P' : F' *) *)
        let F' = T.forSub (F, s)
        let P'' = raisePrg (G', (P, T.coerceSub s), F')
      in
        P''
      end

    let rec raiseF (G, (F, t)) =
      let
        let (G', s) = T.deblockify G
        let F' = raiseFor (G', (F, I.comp (t, T.coerceSub s)))
      in
        F'
      end



  in
    let raisePrg = fn (G, P, F) => raisePrg (G, (P, I.id), F)
    let raiseP = raiseP
    let raiseFor = raiseFor
    let raiseF = raiseF
  end
end (* functor TomegaAbstract *)
