open Basis

(* Abstraction mechanisms form programs and formulas *)

(* Author: Carsten Schuermann *)

module type TOMEGAABSTRACT = sig
  exception Error of string

  val raiseFor :
    IntSyn.dec IntSyn.ctx * (Tomega.for_sml * IntSyn.sub) -> Tomega.for_sml

  val raisePrg :
    IntSyn.dec IntSyn.ctx * Tomega.prg * Tomega.for_sml -> Tomega.prg

  val raiseP : IntSyn.dec IntSyn.ctx * Tomega.prg * Tomega.for_sml -> Tomega.prg

  val raiseF :
    IntSyn.dec IntSyn.ctx * (Tomega.for_sml * IntSyn.sub) -> Tomega.for_sml
end

(* Signature TOMEGAABSTRACT *)
(* Converter from relational representation to a functional
   representation of proof terms *)

(* Author: Carsten Schuermann *)

module TomegaAbstract
    (Global : Global.GLOBAL)
    (Abstract : ABSTRACT)
    (Whnf : Whnf.WHNF)
    (Subordinate : Subordinate.SUBORDINATE) : TOMEGAABSTRACT = struct
  exception Error of string

  module T = Tomega
  module I = IntSyn
  module M = ModeSyn
  module S = Subordinate
  module A = Abstract

  let rec shiftCtx = function
    | I.Null, t -> (I.Null, t)
    | I.Decl (G, D), t ->
        let G', t' = shiftCtx (G, t) in
        (I.Decl (G', I.decSub (D, t')), I.dot1 t')
  (* dotn (t, n) = t'

       Invariant:
       If   Psi0 |- t : Psi
       and  |G| = n   for_sml any G
       then Psi0, G[t] |- t : Psi, G
    *)

  let rec dotn = function t, 0 -> t | t, n -> I.dot1 (dotn (t, n - 1))

  let rec strengthenToSpine = function
    | I.Shift _ (* =0 *), 0, (n, S) -> S
    | I.Dot (I.Idx _ (* = 1 *), t), l, (n, S) ->
        let t' = I.comp (t, I.invShift) in
        strengthenToSpine
          (t', l - 1, (n + 1, I.App (I.Root (I.BVar n, I.Nil), S)))
    | I.Dot (I.Undef, t), l, (n, S) -> strengthenToSpine (t, l - 1, (n + 1, S))
    | I.Shift k, l, (n, S) ->
        strengthenToSpine (I.Dot (I.Idx (k + 1), I.Shift (k + 1)), l, (n, S))
  (* raiseFor (B, (F, t)) = (P', F'))

       Invariant:
       If   Psi, B, G |-  F for_sml
       and  Psi, G', B' |- t : Psi, B, G
       then Psi, G' |-  F' for_sml
       and  F' = raise (B', F[t])   (using subordination)
    *)

  let rec raiseFor = function
    | B', (T.True, t) -> T.True
    | B', (T.And (F1, F2), t) ->
        let F1' = raiseFor (B', (F1, t)) in
        let F2' = raiseFor (B', (F2, t)) in
        T.And (F1', F2')
    | B', (T.Ex ((I.Dec (x, V), Q), F), t) ->
        (*        val (w, S) = subweaken (B', 1, I.targetFam V, I.Nil)     *)
        (* B'  |- w  : B''    *)
        (* B'' |- iw : B'     *)
        (* Psi0, G' |- B'' ctx *)
        (* Psi0, G' |- V' : type *)
        (* Psi, G', x: V' |- B''' ctx *)
        (* Psi, G', x: V', B''' |- t'' :   Psi, G', B' *)
        (* Psi, G', B' |- t : Psi, B, G  *)
        (* Psi, G', x:V', B''' |- t' : Psi, B, G *)
        (* Psi, G', x:V', B''' |- w : Psi,G', x:V', B'''' *)
        (* Psi, G', x:V', B''' |- S : V' [^|B'''|] >> type  *)
        (* Psi, G', x:V', B''' |- U : V[t'] *)
        (* Psi, G', x:V', B''' |- t''' :  Psi, B, G, x:V *)
        (* Psi, G', x:V' |- F' for_sml*)
        let w = S.weaken (B', I.targetFam V) in
        let iw = Whnf.invert w in
        let B'' = Whnf.strengthen (iw, B') in
        let V' = A.raiseType (B'', I.EClo (V, I.comp (t, iw))) in
        let B''', _ = shiftCtx (B', I.shift) in
        let t'' = dotn (I.shift, I.ctxLength B') in
        let t' = I.comp (t, t'') in
        let S = strengthenToSpine (iw, I.ctxLength B', (1, I.Nil)) in
        let U = I.Root (I.BVar (I.ctxLength B''' + 1), S) in
        let t''' = Whnf.dotEta (I.Exp U, t') in
        let F' = raiseFor (B''', (F, t''')) in
        T.Ex ((I.Dec (x, V'), Q), F')
        (* Psi, G', x:V', B''' |- t''' :  Psi, B, G, x:V *)
    | _, (T.All _, _) -> raise Domain
  (* raisePrg (G, P, F) = (P', F'))

       Invariant:
       If   Psi, G |- P in F
       and  Psi |- G : blockctx
       then Psi |- P' in F'
       and  P = raise (G, P')   (using subordination)
       and  F = raise (G, F')   (using subordination)
    *)

  let rec raisePrg = function
    | G, (T.Unit, t), _ -> T.Unit
    | G, (T.PairPrg (P1, P2), t), T.And (F1, F2) ->
        let P1' = raisePrg (G, (P1, t), F1) in
        let P2' = raisePrg (G, (P2, t), F2) in
        T.PairPrg (P1', P2')
    | G, (T.PairExp (U, P), t), T.Ex ((I.Dec (_, V), _), F) ->
        (* G  |- w  : G'    *)
        (* G' |- iw : G     *)
        (* Psi0, G' |- B'' ctx *)
        let w = S.weaken (G, I.targetFam V) in
        let iw = Whnf.invert w in
        let G' = Whnf.strengthen (iw, G) in
        let U' = A.raiseTerm (G', I.EClo (U, I.comp (t, iw))) in
        let P' = raisePrg (G, (P, t), F) in
        T.PairExp (U', P')

  let rec raiseP G P F =
    (*      val P' = T.normalizePrg (P, s) (* G' |- P' : F' *) *)
    let G', s = T.deblockify G in
    let F' = T.forSub (F, s) in
    let P'' = raisePrg (G', (P, T.coerceSub s), F') in
    P''

  let rec raiseF (G, (F, t)) =
    let G', s = T.deblockify G in
    let F' = raiseFor (G', (F, I.comp (t, T.coerceSub s))) in
    F'

  let raisePrg = fun G P F -> raisePrg (G, (P, I.id), F)
  let raiseP = raiseP
  let raiseFor = raiseFor
  let raiseF = raiseF
end

(* functor TomegaAbstract *)
