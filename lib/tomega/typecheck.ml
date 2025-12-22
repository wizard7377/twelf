(* Type checking for_sml Tomega *)

(* Author: Carsten Schuermann *)

(* Modified: Yu Liao *)

module TomegaTypeCheck
    (Abstract : ABSTRACT)
    (TypeCheck : TYPECHECK)
    (Conv : CONV)
    (Whnf : WHNF)
    (Print : PRINT)
    (TomegaPrint : TOMEGAPRINT)
    (Subordinate : SUBORDINATE)
    (Weaken : WEAKEN)
    (TomegaAbstract : TOMEGAABSTRACT) : TOMEGATYPECHECK = struct
  (*! structure IntSyn = IntSyn' !*)

  (*! structure Tomega = Tomega' !*)

  exception Error of string

  module I = IntSyn
  module T = Tomega
  module S = Subordinate
  module TA = TomegaAbstract

  let rec chatter chlev f =
    if !Global.chatter >= chlev then print (f ()) else ()

  let rec normalizeHead = function
    | T.Const lemma, t -> T.Const lemma
    | T.Var k, t -> ( match T.varSub (k, t) with T.Idx k' -> T.Var k')
  (* no other cases can occur *)

  (*    (* inferCon (Psi, (H, t)) = (F', t')

       Invariant:
       If   Psi  |- t : Psi1
       and  Psi1 |- H : F
       then Psi  |- F'[t'] == F[t]
    *)
    fun inferCon (Psi, T.Const lemma) = inferLemma lemma
      | inferCon (Psi, T.Var k) =
          case T.ctxDec (Psi, k) of T.PDec (_, F') => F'
*)

  (* inferSpine (Psi, (S, t1), (F, t2)) = (F', t')

       Invariant:
       If   Psi  |- t1 : Psi1
       and  Psi1 |- S : F' > F''
       and  Psi  |- t2 : Psi2
       and  Psi2 |- F for_sml
       and  Psi  |- F'[t1] == F[t2]
       then Psi  |- F''[t1] == F'[t']
    *)

  let rec inferSpine (Psi, S, Ft) = inferSpineW (Psi, S, T.whnfFor Ft)

  and inferSpineW = function
    | Psi, T.Nil, (F, t) -> (F, t)
    | Psi, T.AppExp (M, S), (T.All ((T.UDec (I.Dec (_, A)), _), F), t) ->
        let _ = chatter 4 (fun () -> "[appExp") in
        let G = T.coerceCtx Psi in
        let _ = TypeCheck.typeCheck (G, (M, I.EClo (A, T.coerceSub t))) in
        let _ = chatter 4 (fun () -> "]") in
        inferSpine (Psi, S, (F, T.Dot (T.Exp M, t)))
    | ( Psi,
        T.AppBlock (I.Bidx k, S),
        (T.All ((T.UDec (I.BDec (_, (cid, s))), _), F2), t2) ) ->
        let (T.UDec (I.BDec (_, (cid', s')))) = T.ctxDec (Psi, k) in
        let G', _ = I.conDecBlock (I.sgnLookup cid') in
        let _ =
          if cid <> cid' then raise (Error "Block label incompatible") else ()
        in
        let s'' = T.coerceSub (T.comp (T.embedSub s, t2)) in
        let _ = Conv.convSub (s', s'') in
        inferSpine (Psi, S, (F2, T.Dot (T.Block (I.Bidx k), t2)))
    | Psi, T.AppPrg (P, S), (T.All ((T.PDec (_, F1, _, _), _), F2), t) ->
        let _ = checkPrg (Psi, (P, (F1, t))) in
        inferSpine (Psi, S, (F2, T.dot1 t))
    | Psi, _, _ -> raise (Error "applied, but not of function type.")

  and inferPrg = function
    | Psi, T.Lam (D, P) ->
        let F = inferPrg (I.Decl (Psi, D), P) in
        T.All ((D, T.Explicit), F)
    | Psi, T.New P ->
        let (T.All ((T.UDec D, _), F)) = inferPrg (Psi, P) in
        TA.raiseF (I.Decl (I.Null, D), (F, I.id))
    | Psi, T.PairExp (U, P) ->
        let V = TypeCheck.infer' (T.coerceCtx Psi, U) in
        let F = inferPrg (Psi, P) in
        T.Ex ((I.Dec (None, V), T.Explicit), F)
    | Psi, T.PairBlock (I.Bidx k, P) ->
        let D = I.ctxLookup (T.coerceCtx Psi, k) in
        let F = inferPrg (Psi, P) in
        T.Ex ((D, T.Explicit), F)
    | Psi, T.PairPrg (P1, P2) ->
        let F1 = inferPrg (Psi, P1) in
        let F2 = inferPrg (Psi, P2) in
        T.And (F1, F2)
    | Psi, T.Unit -> T.True
    | Psi, T.Var k -> (
        match T.ctxDec (Psi, k) with T.PDec (_, F', _, _) -> F')
    | Psi, T.Const c -> inferLemma c
    | Psi, T.Redex (P, S) ->
        let F1 = inferPrg (Psi, P) in
        let F2 = inferSpine (Psi, S, (F1, T.id)) in
        T.forSub F2
    | Psi, T.Rec (D, P) ->
        let _ = checkPrg (I.Decl (Psi, D), (P, (F, T.id))) in
        F
    | Psi, T.Let (D, P1, P2) ->
        let _ = checkPrg (Psi, (P1, (F1, T.id))) in
        let F2 = inferPrg (I.Decl (Psi, D), P2) in
        F2

  and checkPrg (Psi, (P, Ft)) = checkPrgW (Psi, (P, T.whnfFor Ft))

  and checkPrgW = function
    | _, (T.Unit, (T.True, _)) ->
        let _ = chatter 4 (fun () -> "[true]") in
        ()
    | Psi, (T.Const lemma, (F, t)) ->
        convFor (Psi, (inferLemma lemma, T.id), (F, t))
    | Psi, (T.Var k, (F, t)) -> (
        match T.ctxDec (Psi, k) with
        | T.PDec (_, F', _, _) -> convFor (Psi, (F', T.id), (F, t)))
    | Psi, (T.Lam (D, P), (T.All ((T.PDec (x', F1', _, _), _), F2), t)) ->
        let _ = chatter 4 (fun () -> "[lam[p]") in
        let _ = convFor (Psi, (F1, T.id), (F1', t)) in
        let _ = chatter 4 (fun () -> "]") in
        checkPrg (I.Decl (Psi, D), (P, (F2, T.dot1 t)))
    | Psi, (T.Lam (T.UDec D, P), (T.All ((T.UDec D', _), F), t2)) ->
        let _ = chatter 4 (fun () -> "[lam[u]") in
        let _ = Conv.convDec ((D, I.id), (D', T.coerceSub t2)) in
        let _ = chatter 4 (fun () -> "]") in
        checkPrg (I.Decl (Psi, T.UDec D), (P, (F, T.dot1 t2)))
    | Psi, (T.PairExp (M, P), (T.Ex ((I.Dec (x, A), _), F2), t)) ->
        let _ = chatter 4 (fun () -> "[pair [e]") in
        let G = T.coerceCtx Psi in
        let _ = TypeCheck.typeCheck (G, (M, I.EClo (A, T.coerceSub t))) in
        let _ = chatter 4 (fun () -> "]") in
        checkPrg (Psi, (P, (F2, T.Dot (T.Exp M, t))))
    | Psi, (T.PairBlock (I.Bidx k, P), (T.Ex ((I.BDec (_, (cid, s)), _), F2), t))
      ->
        let (T.UDec (I.BDec (_, (cid', s')))) = T.ctxDec (Psi, k) in
        let G', _ = I.conDecBlock (I.sgnLookup cid) in
        let _ =
          if cid' <> cid then raise (Error "Block label mismatch") else ()
        in
        let _ =
          convSub
            (Psi, T.embedSub s', T.comp (T.embedSub s, t), T.revCoerceCtx G')
        in
        checkPrg (Psi, (P, (F2, T.Dot (T.Block (I.Bidx k), t))))
    | Psi, (T.PairPrg (P1, P2), (T.And (F1, F2), t)) ->
        let _ = chatter 4 (fun () -> "[and") in
        let _ = checkPrg (Psi, (P1, (F1, t))) in
        let _ = chatter 4 (fun () -> "...") in
        let _ = checkPrg (Psi, (P2, (F2, t))) in
        let _ = chatter 4 (fun () -> "]") in
        ()
    | Psi, (T.Case Omega, Ft) -> checkCases (Psi, (Omega, Ft))
    | Psi, (T.Rec (D, P), (F', t)) ->
        let _ = chatter 4 (fun () -> "[rec") in
        let _ = convFor (Psi, (F, T.id), (F', t)) in
        let _ = chatter 4 (fun () -> "]\n") in
        checkPrg (I.Decl (Psi, D), (P, (F', t)))
    | Psi, (T.Let (D, P1, P2), (F2, t)) ->
        (* Psi |- F1 == F1' for_sml *)
        let _ = chatter 4 (fun () -> "[let") in
        let _ = checkPrg (Psi, (P1, (F1, T.id))) in
        let _ = chatter 4 (fun () -> ".") in
        let _ = checkPrg (I.Decl (Psi, D), (P2, (F2, T.comp (t, T.shift)))) in
        let _ = chatter 4 (fun () -> "]\n") in
        ()
    | Psi, (T.New P', (F, t)) ->
        (* D'' == D *)
        let _ = chatter 5 (fun () -> "[new1...") in
        let (T.All ((T.UDec D'', _), F')) = inferPrg (Psi, P') in
        let _ = chatter 5 (fun () -> "][new2...") in
        let F'' = TA.raiseF (I.Decl (I.Null, D), (F', I.id)) in
        convFor (Psi, (F'', T.id), (F, t));
        chatter 5 (fun () -> "]\n")
    | Psi, (T.Redex (P1, S2), (F, t)) ->
        let F' = inferPrg (Psi, P1) in
        checkSpine (Psi, S2, (F', T.id), (F, t))
    | Psi, (T.Box (W, P), (T.World (W', F), t)) -> checkPrgW (Psi, (P, (F, t)))

  and checkSpine = function
    | Psi, T.Nil, (F, t), (F', t') -> convFor (Psi, (F, t), (F', t'))
    | Psi, T.AppExp (U, S), (T.All ((T.UDec (I.Dec (_, V)), _), F), t), (F', t')
      ->
        TypeCheck.typeCheck (T.coerceCtx Psi, (U, I.EClo (V, T.coerceSub t)));
        checkSpine (Psi, S, (F, T.Dot (T.Exp U, t)), (F', t'))
    | Psi, T.AppPrg (P, S), (T.All ((T.PDec (_, F1, _, _), _), F2), t), (F', t')
      ->
        checkPrgW (Psi, (P, (F1, t)));
        checkSpine (Psi, S, (F2, T.Dot (T.Undef, t)), (F', t'))
    | Psi, T.AppExp (U, S), (T.FClo (F, t1), t), (F', t') ->
        checkSpine (Psi, T.AppExp (U, S), (F, T.comp (t1, t)), (F', t'))

  and checkCases = function
    | Psi, (T.Cases [], (F2, t2)) -> ()
    | Psi, (T.Cases ((Psi', t', P) :: Omega), (F2, t2)) ->
        (* Psi' |- t' :: Psi *)
        let _ = chatter 4 (fun () -> "[case... ") in
        let _ = chatter 4 (fun () -> "sub... ") in
        let _ = checkSub (Psi', t', Psi) in
        let _ = chatter 4 (fun () -> "prg... ") in
        let t2' = T.comp (t2, t') in
        let _ = checkCtx Psi in
        let _ = checkCtx Psi' in
        let _ = chatter 4 (fun () -> "]") in
        let _ = checkPrg (Psi', (P, (F2, t2'))) in
        let _ = chatter 4 (fun () -> "]\n") in
        let _ = checkCases (Psi, (T.Cases Omega, (F2, t2))) in
        ()

  and inferLemma lemma =
    match T.lemmaLookup lemma with
    | T.ForDec (_, F) -> F
    | T.ValDec (_, _, F) -> F

  and convFor (Psi, Ft1, Ft2) = convForW (Psi, T.whnfFor Ft1, T.whnfFor Ft2)

  and convForW = function
    | _, (T.True, _), (T.True, _) -> ()
    | ( Psi,
        (T.All ((D, _), F1), t1),
        (T.All ((T.UDec (I.Dec (_, A2)), _), F2), t2) ) ->
        let G = T.coerceCtx Psi in
        let s1 = T.coerceSub t1 in
        let s2 = T.coerceSub t2 in
        let _ = Conv.conv ((A1, s1), (A2, s2)) in
        let _ = TypeCheck.typeCheck (G, (I.EClo (A1, s1), I.Uni I.Type)) in
        let _ = TypeCheck.typeCheck (G, (I.EClo (A2, s2), I.Uni I.Type)) in
        let D' = T.decSub (D, t1) in
        let _ = convFor (I.Decl (Psi, D'), (F1, T.dot1 t1), (F2, T.dot1 t2)) in
        ()
    | ( Psi,
        (T.All ((D, _), F1), t1),
        (T.All ((T.UDec (I.BDec (_, (l2, s2))), _), F2), t2) ) ->
        let _ = if l1 <> l2 then raise (Error "Contextblock clash") else () in
        let G', _ = I.conDecBlock (I.sgnLookup l1) in
        let _ =
          convSub
            ( Psi,
              T.comp (T.embedSub s1, t1),
              T.comp (T.embedSub s2, t2),
              T.embedCtx G' )
        in
        let D' = T.decSub (D, t1) in
        let _ = convFor (I.Decl (Psi, D'), (F1, T.dot1 t1), (F2, T.dot1 t2)) in
        ()
    | Psi, (T.Ex ((D, _), F1), t1), (T.Ex ((I.Dec (_, A2), _), F2), t2) ->
        let G = T.coerceCtx Psi in
        let s1 = T.coerceSub t1 in
        let s2 = T.coerceSub t2 in
        let _ = Conv.conv ((A1, s1), (A2, s2)) in
        let _ = TypeCheck.typeCheck (G, (I.EClo (A1, s1), I.Uni I.Type)) in
        let _ = TypeCheck.typeCheck (G, (I.EClo (A2, s2), I.Uni I.Type)) in
        let D' = I.decSub (D, s1) in
        let _ =
          convFor (I.Decl (Psi, T.UDec D'), (F1, T.dot1 t1), (F2, T.dot1 t2))
        in
        ()
    | Psi, (T.Ex ((D, _), F1), t1), (T.Ex ((I.BDec (_, (l2, s2)), _), F2), t2)
      ->
        let _ = if l1 <> l2 then raise (Error "Contextblock clash") else () in
        let G', _ = I.conDecBlock (I.sgnLookup l1) in
        let s1 = T.coerceSub t1 in
        let _ =
          convSub
            ( Psi,
              T.comp (T.embedSub s1, t1),
              T.comp (T.embedSub s2, t2),
              T.embedCtx G' )
        in
        let D' = I.decSub (D, s1) in
        let _ =
          convFor (I.Decl (Psi, T.UDec D'), (F1, T.dot1 t1), (F2, T.dot1 t2))
        in
        ()
    | Psi, (T.And (F1, F1'), t1), (T.And (F2, F2'), t2) ->
        let _ = convFor (Psi, (F1, t1), (F2, t2)) in
        let _ = convFor (Psi, (F1', t1), (F2', t2)) in
        ()
    | ( Psi,
        (T.All ((D, _), F1'), t1),
        (T.All ((T.PDec (_, F2, _, _), _), F2'), t2) ) ->
        let _ = convFor (Psi, (F1, t1), (F2, t2)) in
        let D' = T.decSub (D, t1) in
        let _ =
          convFor (I.Decl (Psi, D'), (F1', T.dot1 t1), (F2', T.dot1 t2))
        in
        ()
    | Psi, (T.World (W1, F1), t1), (T.World (W2, F2), t2) ->
        (* also check that both worlds are equal -- cs Mon Apr 21 01:28:01 2003 *)
        let _ = convFor (Psi, (F1, t1), (F2, t2)) in
        ()
    | _ -> raise (Error "Typecheck error")

  and convSub = function
    | G, T.Shift k1, T.Shift k2, G' ->
        if k1 = k2 then () else raise (Error "Sub not equivalent")
    | G, T.Shift k, s2, G' ->
        convSub (G, T.Dot (T.Idx (k + 1), T.Shift (k + 1)), s2, G')
    | G, s1, T.Shift k, G' ->
        convSub (G, s1, T.Dot (T.Idx (k + 1), T.Shift (k + 1)), G')
    | G, T.Dot (T.Idx k1, s1), T.Dot (T.Idx k2, s2), I.Decl (G', _) ->
        if
          k1 = k2
          (* For s1==s2, the variables in s1 and s2 must refer to the same cell in the context -- Yu Liao *)
        then convSub (G, s1, s2, G')
        else raise (Error "Sub not equivalent")
    | ( G,
        T.Dot (T.Exp M1, s1),
        T.Dot (T.Exp M2, s2),
        I.Decl (G', T.UDec (I.Dec (_, A))) ) ->
        (* checkConv doesn't need context G?? -- Yu Liao *)
        let _ = TypeCheck.checkConv (M1, M2) in
        let _ = TypeCheck.typeCheck (T.coerceCtx G, (M1, A)) in
        convSub (G, s1, s2, G')
    | ( G,
        T.Dot (T.Block (I.Bidx v1), s1),
        T.Dot (T.Block (I.Bidx v2), s2),
        I.Decl (G', T.UDec (I.BDec (_, (l, s)))) ) ->
        let (T.UDec (I.BDec (_, (l1, s11)))) = T.ctxDec (G, v1) in
        let (T.UDec (I.BDec (_, (l2, s22)))) = T.ctxDec (G, v2) in
        let _ = if l1 = l2 then () else raise (Error "Sub not equivalent") in
        let _ = if l1 = l then () else raise (Error "Sub not equivalent") in
        let G'', _ = I.conDecBlock (I.sgnLookup l) in
        let _ =
          convSub (G, T.embedSub s11, T.embedSub s22, T.revCoerceCtx G'')
        in
        let _ = convSub (G, T.embedSub s11, T.embedSub s, T.revCoerceCtx G'') in
        convSub (G, s1, s2, G')
    | ( G,
        T.Dot (T.Prg P1, s1),
        T.Dot (T.Prg P2, s2),
        I.Decl (G', T.PDec (_, F, _, _)) ) ->
        let _ = isValue P1 in
        let _ = isValue P2 in
        let _ = convValue (G, P1, P2, F) in
        convSub (G, s1, s2, G')
    | ( G,
        T.Dot (T.Idx k1, s1),
        T.Dot (T.Exp M2, s2),
        I.Decl (G', T.UDec (I.Dec (_, A))) ) ->
        let _ = TypeCheck.checkConv (I.Root (I.BVar k1, I.Nil), M2) in
        let _ = TypeCheck.typeCheck (T.coerceCtx G, (M2, A)) in
        convSub (G, s1, s2, G')
    | ( G,
        T.Dot (T.Exp M1, s1),
        T.Dot (T.Idx k2, s2),
        I.Decl (G', T.UDec (I.Dec (_, A))) ) ->
        let _ = TypeCheck.checkConv (M1, I.Root (I.BVar k2, I.Nil)) in
        let _ = TypeCheck.typeCheck (T.coerceCtx G, (M1, A)) in
        convSub (G, s1, s2, G')
    | ( G,
        T.Dot (T.Idx k1, s1),
        T.Dot (T.Prg P2, s2),
        I.Decl (G', T.PDec (_, F, _, _)) ) ->
        let _ = isValue P2 in
        let _ = convValue (G, T.Var k1, P2, F) in
        convSub (G, s1, s2, G')
    | ( G,
        T.Dot (T.Prg P1, s1),
        T.Dot (T.Idx k2, s2),
        I.Decl (G', T.PDec (_, F, _, _)) ) ->
        let _ = isValue P1 in
        let _ = convValue (G, P1, T.Var k2, F) in
        convSub (G, s1, s2, G')

  and convValue (G, P1, P2, F) = ()

  and checkFor = function
    | Psi, (T.True, _) -> ()
    | Psi, (T.All ((D, _), F2), t) ->
        checkFor (Psi, (F1, t));
        checkFor (I.Decl (Psi, D), (F2, T.dot1 t))
    | Psi, (T.All ((D', _), F), t) ->
        TypeCheck.checkDec (T.coerceCtx Psi, (D, T.coerceSub t));
        checkFor (I.Decl (Psi, D'), (F, T.dot1 t))
    | Psi, (T.Ex ((D, _), F), t) ->
        TypeCheck.checkDec (T.coerceCtx Psi, (D, T.coerceSub t));
        checkFor (I.Decl (Psi, T.UDec D), (F, T.dot1 t))
    | Psi, (T.And (F1, F2), t) ->
        checkFor (Psi, (F1, t));
        checkFor (Psi, (F2, t))
    | Psi, (T.FClo (F, t'), t) -> checkFor (Psi, (F, T.comp (t', t)))
    | Psi, (T.World (W, F), t) -> checkFor (Psi, (F, t))

  and checkCtx = function
    | I.Null -> ()
    | I.Decl (Psi, T.UDec D) ->
        checkCtx Psi;
        TypeCheck.checkDec (T.coerceCtx Psi, (D, I.id))
    | I.Decl (Psi, T.PDec (_, F, _, _)) ->
        checkCtx Psi;
        checkFor (Psi, (F, T.id))

  and checkSub = function
    | I.Null, T.Shift 0, I.Null -> ()
    | I.Decl (G, D), T.Shift k, I.Null ->
        if k > 0 then checkSub (G, T.Shift (k - 1), I.Null)
        else raise (Error "Sub is not well typed!")
    | G, T.Shift k, G' ->
        checkSub (G, T.Dot (T.Idx (k + 1), T.Shift (k + 1)), G')
    | G, T.Dot (T.Idx k, s'), I.Decl (G', T.UDec (I.Dec (_, A))) ->
        let _ = checkSub (G, s', G') in
        let (T.UDec (I.Dec (_, A'))) = T.ctxDec (G, k) in
        if Conv.conv ((A', I.id), (A, T.coerceSub s')) then ()
        else raise (Error "Sub isn't well typed!")
    | G, T.Dot (T.Idx k, s'), I.Decl (G', T.UDec (I.BDec (l, (_, s)))) ->
        let _ = checkSub (G, s', G') in
        let (T.UDec (I.BDec (l1, (_, s1)))) = T.ctxDec (G, k) in
        if l <> l1 then raise (Error "Sub isn't well typed!")
        else if Conv.convSub (I.comp (s, T.coerceSub s'), s1) then ()
        else raise (Error "Sub isn't well typed!")
    | G, T.Dot (T.Idx k, s), I.Decl (G', T.PDec (_, F', _, _)) ->
        let _ = checkSub (G, s, G') in
        let (T.PDec (_, F1, _, _)) = T.ctxDec (G, k) in
        convFor (G, (F1, T.id), (F', s))
    | G, T.Dot (T.Exp M, s), I.Decl (G', T.UDec (I.Dec (_, A))) ->
        let _ = checkSub (G, s, G') in
        TypeCheck.typeCheck (T.coerceCtx G, (M, I.EClo (A, T.coerceSub s)))
    | Psi, T.Dot (T.Prg P, t), I.Decl (Psi', T.PDec (_, F', _, _)) ->
        let _ = chatter 4 (fun () -> "$") in
        let _ = checkSub (Psi, t, Psi') in
        let _ = isValue P in
        checkPrg (Psi, (P, (F', t)))
    | Psi, T.Dot (T.Block B, t), I.Decl (Psi', T.UDec (I.BDec (l2, (c, s2)))) ->
        (* Psi |- t : Psi' *)
        (* Psi' |- s2 : SOME variables of c *)
        (* Psi |- s2 : G *)
        let _ = chatter 4 (fun () -> "$") in
        let _ = checkSub (Psi, t, Psi') in
        let G, L = I.constBlock c in
        let _ = TypeCheck.typeCheckSub (T.coerceCtx Psi', s2, G) in
        checkBlock (Psi, (B, (c, I.comp (s2, T.coerceSub t))))
    | Psi, T.Dot _, I.Null -> raise (Error "Sub is not well typed")

  and checkBlock = function
    | Psi, (I.Bidx v, (c2, s2)) ->
        let (T.UDec (I.BDec (l1, (c1, s1)))) = T.ctxDec (Psi, v) in
        if c1 <> c2 then raise (Error "Sub isn't well typed!")
        else if Conv.convSub (s2, s1) then ()
        else raise (Error "Sub isn't well typed!")
    | Psi, (I.Inst UL, (c2, s2)) ->
        (* Psi |- s2 : G *)
        let G, L = I.constBlock c2 in
        let _ = TypeCheck.typeCheckSub (T.coerceCtx Psi, s2, G) in
        checkInst (Psi, UL, (1, L, s2))

  and checkInst = function
    | Psi, [], (_, [], _) -> ()
    | Psi, U :: UL, (n, D :: L, s2) ->
        let G = T.coerceCtx Psi in
        let (I.Dec (_, V)) = I.decSub (D, s2) in
        let _ = TypeCheck.typeCheck (G, (U, V)) in
        checkInst (Psi, UL, (n + 1, L, I.dot1 s2))

  and isValue = function
    | T.Var _ -> ()
    | T.PClo (T.Lam _, _) -> ()
    | T.PairExp (M, P) -> isValue P
    | T.PairBlock _ -> ()
    | T.PairPrg (P1, P2) ->
        isValue P1;
        isValue P2
    | T.Unit -> ()
    | T.Rec _ -> ()
    | T.Const lemma -> (
        match T.lemmaLookup lemma with
        | T.ForDec _ -> raise (Error "Lemma isn't a value")
        | T.ValDec (_, P, _) -> isValue P)
    | _ -> raise (Error "P isn't Value!")
  (*  remove later!
    and isValue (T.Lam _) = ()
      | isValue (T.PairExp (M, P)) = isValue P
      | isValue (T.PairBlock _ ) = ()
      | isValue (T.PairPrg (P1, P2)) = (isValue P1; isValue P2)
      | isValue T.Unit = ()
      | isValue (T.Root ((T.Const lemma), T.Nil)) = (* could lemma be a VALUE? -- Yu Liao *)
        ( case (T.lemmaLookup lemma) of
              T.ForDec _ => raise Error "Lemma isn't a value"
            | T.ValDec(_,P,_) => isValue P )

      | isValue (T.Root ((T.Var k), T.Nil)) = ()
      | isValue (T.Rec _) = ()

      (* ABP 1/23/03 *)
      | isValue (T.EVar _) = raise Error "It is an EVar"

      | isValue _ = raise Error "P isn't Value!"
*)

  let rec check (Psi, (P, F)) = checkPrg (Psi, (P, (F, T.id)))
  let checkPrg = fun (Psi, (P, F)) -> checkPrg (Psi, (P, (F, T.id)))
  let checkSub = checkSub
  let checkFor = fun (Psi, F) -> checkFor (Psi, (F, T.id))
  let checkCtx = checkCtx
end
(* Type checking for_sml functional proof term calculus *)

(* Author: Carsten Schuermann *)

(* Modified: Yu Liao *)

module type TOMEGATYPECHECK = sig
  exception Error of string

  val checkCtx : Tomega.dec IntSyn.ctx -> unit
  val checkFor : Tomega.dec IntSyn.ctx * Tomega.for_sml -> unit
  val checkPrg : Tomega.dec IntSyn.ctx * (Tomega.prg * Tomega.for_sml) -> unit

  val checkSub :
    Tomega.dec IntSyn.ctx * Tomega.sub * Tomega.dec IntSyn.ctx -> unit
end

(* Signature TOMEGATYPECHECK *)
