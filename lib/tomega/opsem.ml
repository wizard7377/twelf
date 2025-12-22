(* Internal syntax for_sml functional proof term calculus *)

(* Author: Carsten Schuermann, Adam Poswolsky *)

module Opsem
    (Whnf : WHNF)
    (Abstract : ABSTRACT)
    (Subordinate : SUBORDINATE)
    (TomegaTypeCheck : TOMEGATYPECHECK)
    (TomegaPrint : TOMEGAPRINT)
    (Unify : UNIFY) : OPSEM = struct
  module T = Tomega
  module I = IntSyn
  module S = Subordinate
  module A = Abstract

  exception Error of string
  exception Abort
  (*  local -- removed ABP 1/19/03 *)

  exception NoMatch
  (*
 matchPrg is used to see if two values can be 'unified' for_sml
   purpose of matching case

 matchPrg (Psi, P1, P2) = ()

    Invariant:
    If P1 has no EVARs and P2 possibly does.
    and Psi  |- P1 :: F
    and Psi |- P1 value
    and Psi |- P2 :: F
    and Psi |- P2 value
     then if Psi |- P1 == P2 matchPrg terminates
       otherwise exception NoMatch is raised
*)

  let rec matchPrg (Psi, P1, P2) =
    matchVal (Psi, (P1, T.id), T.normalizePrg (P2, T.id))

  and matchVal = function
    | Psi, (T.Unit, _), T.Unit -> ()
    | Psi, (T.PairPrg (P1, P1'), t1), T.PairPrg (P2, P2') ->
        matchVal (Psi, (P1, t1), P2);
        matchVal (Psi, (P1', t1), P2')
    | Psi, (T.PairBlock (B1, P1), t1), T.PairBlock (B2, P2) -> (
        matchVal (Psi, (P1, t1), P2);
        try
          Unify.unifyBlock (T.coerceCtx Psi, I.blockSub (B1, T.coerceSub t1), B2)
        with Unify.Unify _ -> raise NoMatch)
    | Psi, (T.PairExp (U1, P1), t1), T.PairExp (U2, P2) -> (
        matchVal (Psi, (P1, t1), P2);
        try Unify.unify (T.coerceCtx Psi, (U1, T.coerceSub t1), (U2, I.id))
        with Unify.Unify _ -> raise NoMatch)
    | Psi, (T.PClo (P, t1'), t1), Pt -> matchVal (Psi, (P, T.comp (t1', t1)), Pt)
    | Psi, (P', t1), T.PClo (T.PClo (P, t2), t3) ->
        matchVal (Psi, (P', t1), T.PClo (P, T.comp (t2, t3)))
    | Psi, (P', t1), T.PClo (T.EVar (_, r, _, _, _, _), t2) ->
        let iw = T.invertSub t2 in
        (* ABP -- just make sure this is right *)
        r := Some (T.PClo (P', T.comp (t1, iw)))
    | Psi, (P', t1), T.EVar (_, r, _, _, _, _) -> r := Some (T.PClo (P', t1))
    | Psi, (V, t), T.EVar (D, r, F, _, _, _) -> matchVal (Psi, (V, t), P)
    | _ -> raise NoMatch

  let rec append = function
    | G1, I.Null -> G1
    | G1, I.Decl (G2, D) -> I.Decl (append (G1, G2), D)

  and raisePrg = function
    | Psi, G, T.Unit -> T.Unit
    | Psi, G, T.PairPrg (P1, P2) ->
        let P1' = raisePrg (Psi, G, P1) in
        let P2' = raisePrg (Psi, G, P2) in
        T.PairPrg (P1', P2')
    | Psi, G, T.PairExp (U, P) ->
        (* this is a real time sink, it would be much better if we did not have to
      compute the type information of U,
      more thought is required
   *)
        (* G  |- w  : G'    *)
        (* G' |- iw : G     *)
        (* Psi0, G' |- B'' ctx *)
        let V = TypeCheck.infer' (append (T.coerceCtx Psi, G), U) in
        let w = S.weaken (G, I.targetFam V) in
        let iw = Whnf.invert w in
        let G' = Whnf.strengthen (iw, G) in
        let U' = A.raiseTerm (G', I.EClo (U, iw)) in
        let P' = raisePrg (Psi, G, P) in
        T.PairExp (U', P')

  and evalPrg = function
    | Psi, (T.Unit, t) -> T.Unit
    | Psi, (T.PairExp (M, P), t) ->
        T.PairExp (I.EClo (M, T.coerceSub t), evalPrg (Psi, (P, t)))
    | Psi, (T.PairBlock (B, P), t) ->
        T.PairBlock (I.blockSub (B, T.coerceSub t), evalPrg (Psi, (P, t)))
    | Psi, (T.PairPrg (P1, P2), t) ->
        T.PairPrg (evalPrg (Psi, (P1, t)), evalPrg (Psi, (P2, t)))
    | Psi, (T.Redex (P, S), t) -> evalRedex (Psi, evalPrg (Psi, (P, t)), (S, t))
    | Psi, (T.Var k, t) -> (
        match T.varSub (k, t) with T.Prg P -> evalPrg (Psi, (P, T.id)))
    | Psi, (T.Const lemma, t) -> evalPrg (Psi, (T.lemmaDef lemma, t))
    | Psi, (T.Lam (D, P), t) ->
        let D' = T.decSub (D, t) in
        T.Lam (D', evalPrg (I.Decl (Psi, D'), (P, T.dot1 t)))
    | Psi, (T.Lam (D, P), t) -> T.Lam (T.decSub (D, t), T.PClo (P, T.dot1 t))
    | Psi, (P', t) -> evalPrg (Psi, (P, T.Dot (T.Prg (T.PClo (P', t)), t)))
    | Psi, (T.PClo (P, t'), t) -> evalPrg (Psi, (P, T.comp (t', t)))
    | Psi, (T.Case (T.Cases O), t') -> match_ (Psi, t', T.Cases (rev O))
    | Psi, (T.EVar (D, r, F, _, _, _), t) -> evalPrg (Psi, (P, t))
    | Psi, (T.Let (D, P1, P2), t) ->
        let V = evalPrg (Psi, (P1, t)) in
        let V' = evalPrg (Psi, (P2, T.Dot (T.Prg V, t))) in
        V'
    | Psi, (T.New (T.Lam (D, P)), t) ->
        (* unnecessary naming, remove later --cs *)
        let D' = T.decSub (D, t) in
        let (T.UDec D'') = D' in
        let D''' = T.UDec (Names.decName (T.coerceCtx Psi, D'')) in
        let V = evalPrg (I.Decl (Psi, D'''), (P, T.dot1 t)) in
        let B = T.coerceCtx (I.Decl (I.Null, D''')) in
        let G, t' = T.deblockify B in
        let newP = raisePrg (Psi, G, T.normalizePrg (V, t')) in
        newP
    | Psi, (T.Box (W, P), t) -> evalPrg (Psi, (P, t))
    | Psi, (T.Choose P, t) ->
        (* This function was imported from cover.fun   -- cs Thu Mar 20 11:47:06 2003 *)
        (* substtospine' (s, G, T) = S @ T
                If   G' |- s : G
                then G' |- S : {{G}} a >> a  for_sml arbitrary a
                    {{G}} erases void declarations in G
              *)
        let rec substToSpine' = function
          | I.Shift n, I.Null, T -> T
          | I.Shift n, G, T ->
              substToSpine' (I.Dot (I.Idx (n + 1), I.Shift (n + 1)), G, T)
          | I.Dot (I.Exp U, s), I.Decl (G, V), T ->
              substToSpine' (s, G, T.AppExp (U, T))
          | I.Dot (I.Idx n, s), I.Decl (G, I.Dec (_, V)), T ->
              let Us, _ =
                Whnf.whnfEta ((I.Root (I.BVar n, I.Nil), I.id), (V, I.id))
              in
              substToSpine' (s, G, T.AppExp (I.EClo Us, T))
        in
        let rec choose = function
          | k, I.Null -> raise Abort
          | k, I.Decl (Psi', T.PDec _) -> choose (k + 1, Psi')
          | k, I.Decl (Psi', T.UDec (I.Dec _)) -> choose (k + 1, Psi')
          | k, I.Decl (Psi', T.UDec (I.BDec (_, (l1, s1)))) -> (
              let Gsome, Gpi = I.constBlock l1 in
              let S = substToSpine' (s1, Gsome, T.AppBlock (I.Bidx k, T.Nil)) in
              try evalPrg (Psi, (T.Redex (T.PClo (P, t), S), T.id))
              with Abort -> choose (k + 1, Psi'))
        in
        choose (1, Psi)

  and match_ = function
    | Psi, t1, T.Cases ((Psi', t2, P) :: C) -> (
        (* val I.Null = Psi *)
        (* Psi |- t : Psi' *)
        (* Psi' |- t2 . shift(k) : Psi'' *)
        let t = createVarSub (Psi, Psi') in
        let t' = T.comp (t2, t) in
        (* Note that since we are missing the shift(k), it is possible
         * that t' has extra DOTs in there that weren't removed *)
        try
          matchSub (Psi, t1, t');
          evalPrg (Psi, (P (*T.normalizeSub*), t))
        with NoMatch -> match_ (Psi, t1, T.Cases C))
    | Psi, t1, T.Cases [] -> raise Abort

  and createVarSub = function
    | Psi, I.Null -> T.Shift (I.ctxLength Psi)
    | Psi, Psi'' ->
        let t = createVarSub (Psi, Psi') in
        let t' =
          T.Dot (T.Prg (T.newEVarTC (Psi, T.forSub (F, t), None, None)), t)
        in
        t'
    | Psi, I.Decl (Psi', T.UDec (I.Dec (name, V))) ->
        let t = createVarSub (Psi, Psi') in
        T.Dot
          ( T.Exp
              (I.EVar
                 (ref None, T.coerceCtx Psi, I.EClo (V, T.coerceSub t), ref [])),
            t )
    | Psi, I.Decl (Psi', T.UDec (I.BDec (name, (cid, s)))) ->
        let t = createVarSub (Psi, Psi') in
        T.Dot
          ( T.Block (I.LVar (ref None, I.id, (cid, I.comp (s, T.coerceSub t)))),
            t )

  and matchSub = function
    | Psi, _, T.Shift _ -> ()
    | Psi, T.Shift n, t ->
        matchSub (Psi, T.Dot (T.Idx (n + 1), T.Shift (n + 1)), t)
    | Psi, T.Dot (T.Exp U1, t1), T.Dot (T.Exp U2, t2) -> (
        matchSub (Psi, t1, t2);
        try Unify.unify (T.coerceCtx Psi, (U1, I.id), (U2, I.id))
        with Unify.Unify s -> raise NoMatch)
    | Psi, T.Dot (T.Exp U1, t1), T.Dot (T.Idx k, t2) -> (
        matchSub (Psi, t1, t2);
        try
          Unify.unify
            (T.coerceCtx Psi, (U1, I.id), (I.Root (I.BVar k, I.Nil), I.id))
        with Unify.Unify _ -> raise NoMatch)
    | Psi, T.Dot (T.Idx k, t1), T.Dot (T.Exp U2, t2) -> (
        matchSub (Psi, t1, t2);
        try
          Unify.unify
            (T.coerceCtx Psi, (I.Root (I.BVar k, I.Nil), I.id), (U2, I.id))
        with Unify.Unify _ -> raise NoMatch)
    | Psi, T.Dot (T.Prg P1, t1), T.Dot (T.Prg P2, t2) ->
        matchSub (Psi, t1, t2);
        matchPrg (Psi, P1, P2)
    | Psi, T.Dot (T.Prg P1, t1), T.Dot (T.Idx k, t2) ->
        matchSub (Psi, t1, t2);
        matchPrg (Psi, P1, T.Var k)
    | Psi, T.Dot (T.Idx k, t1), T.Dot (T.Prg P2, t2) ->
        matchSub (Psi, t1, t2);
        matchPrg (Psi, T.Var k, P2)
    | Psi, T.Dot (T.Idx k1, t1), T.Dot (T.Idx k2, t2) ->
        if k1 = k2 then matchSub (Psi, t1, t2) else raise NoMatch
    | Psi, T.Dot (T.Idx k, t1), T.Dot (T.Block (I.LVar (r, s1, (c, s2))), t2) ->
        let s1' = Whnf.invert s1 in
        let _ = r := Some (I.blockSub (I.Bidx k, s1')) in
        matchSub (Psi, t1, t2)
    | Psi, T.Dot (T.Block B, t1), T.Dot (T.Block (I.LVar (r, s1, (c, s2))), t2)
      ->
        let s1' = Whnf.invert s1 in
        let _ = r := Some (I.blockSub (B, s1')) in
        matchSub (Psi, t1, t2)

  and evalRedex = function
    | Psi, V, (T.Nil, _) -> V
    | Psi, V, (T.SClo (S, t1), t2) -> evalRedex (Psi, V, (S, T.comp (t1, t2)))
    | Psi, T.Lam (T.UDec (I.Dec (_, A)), P'), (T.AppExp (U, S), t) ->
        let V =
          evalPrg (Psi, (P', T.Dot (T.Exp (I.EClo (U, T.coerceSub t)), T.id)))
        in
        evalRedex (Psi, V, (S, t))
    | Psi, T.Lam (T.UDec _, P'), (T.AppBlock (B, S), t) ->
        evalRedex
          ( Psi,
            evalPrg
              (Psi, (P', T.Dot (T.Block (I.blockSub (B, T.coerceSub t)), T.id))),
            (S, t) )
    | Psi, T.Lam (T.PDec _, P'), (T.AppPrg (P, S), t) ->
        let V = evalPrg (Psi, (P, t)) in
        let V' = evalPrg (Psi, (P', T.Dot (T.Prg V, T.id))) in
        evalRedex (Psi, V', (S, t))
  (* topLevel (Psi, d, (P, t))

       Invariant:
       Psi |- t : Psi'
       Psi' |- P :: F
       d = | Psi' |

    *)

  let rec topLevel = function
    | Psi, d, (T.Unit, t) -> ()
    | Psi, d, (T.Let (D', P1, T.Case Cs), t) ->
        (* printLF (G, s, G') k = ()
             Invariant:
             G |- s : G'
          *)
        let rec printLF = function
          | (_, _, _), 0 -> ()
          | (G, I.Dot (I.Exp U, s'), I.Decl (G', I.Dec (Some name, V))), k ->
              let _ = printLF (G, s', G') (k - 1) in
              print
                ("def " ^ name ^ " = "
                ^ Print.expToString (G, U)
                ^ " : "
                ^ Print.expToString (G, I.EClo (V, s'))
                ^ "\n")
        in
        let rec match_ (Psi, t1, T.Cases ((Psi', t2, P) :: C)) =
          (* Psi |- t : Psi' *)
          (* Psi' |- t2 . shift(k) : Psi'' *)
          (* Psi |- t'' : Psi' *)
          let t = createVarSub (Psi, Psi') in
          let t' = T.comp (t2, t) in
          let m = I.ctxLength Psi' in
          let _ = matchSub (Psi, t1, t') in
          let t'' =
            (* T.normalizeSub *)
            t
          in
          let _ =
            printLF (T.coerceCtx Psi, T.coerceSub t'', T.coerceCtx Psi') (m - d)
          in
          topLevel (Psi, m, (P, t''))
        in
        let V = evalPrg (Psi, (P1, t)) in
        let V' = match_ (Psi, T.Dot (T.Prg V, t), Cs) in
        V'
    | Psi, d, (T.Let (D, T.Lam (D', P1), P2), t) ->
        let _ = print ("new " ^ name ^ "\n") in
        let D'' = T.decSub (D', t) in
        let _ = topLevel (I.Decl (Psi, D''), d + 1, (P1, T.dot1 t)) in
        ()
    | Psi, d, (T.Let (D, P1, P2), t) ->
        let (T.PDec (Some name, F, _, _)) = D in
        let V = evalPrg (Psi, (P1, t)) in
        let _ =
          print
            ("val " ^ name ^ " = "
            ^ TomegaPrint.prgToString (Psi, V)
            ^ " :: "
            ^ TomegaPrint.forToString (Psi, F)
            ^ "\n")
        in
        let V' = topLevel (Psi, d + 1, (P2, T.Dot (T.Prg V, t))) in
        V'
  (* in -- removed local *)

  let evalPrg = fun P -> evalPrg (I.Null, (P, T.id))
  let topLevel = fun P -> topLevel (I.Null, 0, (P, T.id))
  (* end -- removed local *)
end
(* Operational Semantics for_sml Delphin *)

(* Author: Carsten Schuermann *)

module type OPSEM = sig
  (*! structure IntSyn : INTSYN !*)
  (*! structure Tomega : TOMEGA !*)
  exception NoMatch

  val evalPrg : Tomega.prg -> Tomega.prg
  val topLevel : Tomega.prg -> unit
  val createVarSub : Tomega.dec IntSyn.ctx * Tomega.dec IntSyn.ctx -> Tomega.sub
  val matchSub : Tomega.dec IntSyn.ctx * Tomega.sub * Tomega.sub -> unit
end
