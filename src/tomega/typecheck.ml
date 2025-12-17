TomegaTypeCheck  Abstract ABSTRACT    TypeCheck TYPECHECK    Conv CONV    Whnf WHNF    Print PRINT    TomegaPrint TOMEGAPRINT    Subordinate SUBORDINATE    Weaken WEAKEN    TomegaAbstract TOMEGAABSTRACT     TOMEGATYPECHECK  struct (*! structure IntSyn = IntSyn' !*)
(*! structure Tomega = Tomega' !*)
exception module module module module let rec chatterchlevf if ! chatter >= chlev then print (f ()) else ()let rec normalizeHead(const lemma,  , t) const lemma normalizeHead(var k,  , t) (match varSub (k,  , t) with idx (k') -> var (k'))(* no other cases can occur *)
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
       and  Psi2 |- F for
       and  Psi  |- F'[t1] == F[t2]
       then Psi  |- F''[t1] == F'[t']
    *)
let rec inferSpine(psi,  , s,  , ft) inferSpineW (psi,  , s,  , whnfFor ft) inferSpineW(psi,  , nil,  , (f,  , t)) (f,  , t) inferSpineW(psi,  , appExp (m,  , s),  , (all ((uDec (dec (_,  , a)),  , _),  , f),  , t)) let let  inlet  inlet  inlet  in in inferSpine (psi,  , s,  , (f,  , dot (exp (m),  , t))) inferSpineW(psi,  , appBlock (bidx k,  , s),  , (all ((uDec (bDec (_,  , (cid,  , s))),  , _),  , f2),  , t2)) let let  inlet  inlet  inlet  inlet  in in inferSpine (psi,  , s,  , (f2,  , dot (block (bidx k),  , t2))) inferSpineW(psi,  , appPrg (p,  , s),  , (all ((pDec (_,  , f1,  , _,  , _),  , _),  , f2),  , t)) let let  in in inferSpine (psi,  , s,  , (f2,  , dot1 t)) inferSpineW(psi,  , _,  , _) raise (error "applied, but not of function type.") inferPrg(psi,  , lam (d,  , p)) let let  in in all ((d,  , explicit),  , f) inferPrg(psi,  , new p) let let  in in raiseF (decl (null,  , d),  , (f,  , id)) inferPrg(psi,  , pairExp (u,  , p)) let let  inlet  in in ex ((dec (nONE,  , v),  , explicit),  , f) inferPrg(psi,  , pairBlock (bidx k,  , p)) let let  inlet  in in ex ((d,  , explicit),  , f) inferPrg(psi,  , pairPrg (p1,  , p2)) let let  inlet  in in and (f1,  , f2) inferPrg(psi,  , unit) true inferPrg(psi,  , var k) (match ctxDec (psi,  , k) with pDec (_,  , f',  , _,  , _) -> f') inferPrg(psi,  , const c) inferLemma c inferPrg(psi,  , redex (p,  , s)) let let  inlet  in in forSub f2 inferPrg(psi,  , rec (d as pDec (_,  , f,  , _,  , _),  , p)) let let  in in f inferPrg(psi,  , let (d as pDec (_,  , f1,  , _,  , _),  , p1,  , p2)) let let  inlet  in in f2(* checkPrg (Psi, P, F) = ()

       Invariant:
       If   Psi  |- t1 : Psi1
       and  Psi1 |- P : F'
       and  Psi  |- F for     (F in normal form)
       and  P does not contain any P closures
       then checkPrg returns () iff F'[t1] == F[id]
    *)
 checkPrg(psi,  , (p,  , ft)) checkPrgW (psi,  , (p,  , whnfFor ft)) checkPrgW(_,  , (unit,  , (true,  , _))) let let  in in () checkPrgW(psi,  , (const lemma,  , (f,  , t))) convFor (psi,  , (inferLemma lemma,  , id),  , (f,  , t)) checkPrgW(psi,  , (var k,  , (f,  , t))) (match ctxDec (psi,  , k) with pDec (_,  , f',  , _,  , _) -> convFor (psi,  , (f',  , id),  , (f,  , t))) checkPrgW(psi,  , (lam (d as pDec (x,  , f1,  , _,  , _),  , p),  , (all ((pDec (x',  , f1',  , _,  , _),  , _),  , f2),  , t))) let let  inlet  inlet  in in checkPrg (decl (psi,  , d),  , (p,  , (f2,  , dot1 t))) checkPrgW(psi,  , (lam (uDec d,  , p),  , (all ((uDec d',  , _),  , f),  , t2))) let let  inlet  inlet  in in checkPrg (decl (psi,  , uDec d),  , (p,  , (f,  , dot1 t2))) checkPrgW(psi,  , (pairExp (m,  , p),  , (ex ((dec (x,  , a),  , _),  , f2),  , t))) let let  inlet  inlet  inlet  in in checkPrg (psi,  , (p,  , (f2,  , dot (exp m,  , t)))) checkPrgW(psi,  , (pairBlock (bidx k,  , p),  , (ex ((bDec (_,  , (cid,  , s)),  , _),  , f2),  , t))) let let  inlet  inlet  inlet  in in checkPrg (psi,  , (p,  , (f2,  , dot (block (bidx k),  , t)))) checkPrgW(psi,  , (pairPrg (p1,  , p2),  , (and (f1,  , f2),  , t))) let let  inlet  inlet  inlet  inlet  in in () checkPrgW(psi,  , (case omega,  , ft)) checkCases (psi,  , (omega,  , ft)) checkPrgW(psi,  , (rec (d as pDec (x,  , f,  , _,  , _),  , p),  , (f',  , t))) let let  inlet  inlet  in in checkPrg (decl (psi,  , d),  , (p,  , (f',  , t))) checkPrgW(psi,  , (let (d as pDec (_,  , f1,  , _,  , _),  , p1,  , p2),  , (f2,  , t))) let let  inlet  in(* Psi |- F1 == F1' for *)
let  inlet  inlet  in in () checkPrgW(psi,  , (new (p' as lam (uDec (d as bDec (_,  , (cid,  , s))),  , p)),  , (f,  , t))) let let  inlet  in(* D'' == D *)
let  inlet  in in (convFor (psi,  , (f'',  , id),  , (f,  , t)); chatter 5 (fun () -> "]\n")) checkPrgW(psi,  , (redex (p1,  , s2),  , (f,  , t))) let let  in in checkSpine (psi,  , s2,  , (f',  , id),  , (f,  , t)) checkPrgW(psi,  , (box (w,  , p),  , (world (w',  , f),  , t))) checkPrgW (psi,  , (p,  , (f,  , t)))(* don't forget to check if the worlds match up --cs Mon Apr 21 01:51:58 2003 *)
 checkSpine(psi,  , nil,  , (f,  , t),  , (f',  , t')) convFor (psi,  , (f,  , t),  , (f',  , t')) checkSpine(psi,  , appExp (u,  , s),  , (all ((uDec (dec (_,  , v)),  , _),  , f),  , t),  , (f',  , t')) (typeCheck (coerceCtx psi,  , (u,  , eClo (v,  , coerceSub t))); checkSpine (psi,  , s,  , (f,  , dot (exp u,  , t)),  , (f',  , t'))) checkSpine(psi,  , appPrg (p,  , s),  , (all ((pDec (_,  , f1,  , _,  , _),  , _),  , f2),  , t),  , (f',  , t')) (checkPrgW (psi,  , (p,  , (f1,  , t))); checkSpine (psi,  , s,  , (f2,  , dot (undef,  , t)),  , (f',  , t'))) checkSpine(psi,  , appExp (u,  , s),  , (fClo (f,  , t1),  , t),  , (f',  , t')) checkSpine (psi,  , appExp (u,  , s),  , (f,  , comp (t1,  , t)),  , (f',  , t'))(* checkCases (Psi, (Omega, (F, t2))) = ()
       Invariant:
       and  Psi |- Omega : F'
       and  Psi |- F' for
       then checkCases returns () iff Psi |- F' == F [t2] formula
    *)
 checkCases(psi,  , (cases nil,  , (f2,  , t2))) () checkCases(psi,  , (cases ((psi',  , t',  , p) :: omega),  , (f2,  , t2))) let (* Psi' |- t' :: Psi *)
let  inlet  inlet  inlet  inlet  inlet  inlet  inlet  inlet  inlet  inlet  in in () inferLemmalemma (match (lemmaLookup lemma) with forDec (_,  , f) -> f valDec (_,  , _,  , f) -> f)(* convFor (Psi, (F1, t1), (F2, t2)) = ()

       Invariant:
       If   Psi |- t1 :: Psi1
       and  Ps1 |- F1 for
    *)
 convFor(psi,  , ft1,  , ft2) convForW (psi,  , whnfFor ft1,  , whnfFor ft2) convForW(_,  , (true,  , _),  , (true,  , _)) () convForW(psi,  , (all ((d as uDec (dec (_,  , a1)),  , _),  , f1),  , t1),  , (all ((uDec (dec (_,  , a2)),  , _),  , f2),  , t2)) let let  inlet  inlet  inlet  inlet  inlet  inlet  inlet  in in () convForW(psi,  , (all ((d as uDec (bDec (_,  , (l1,  , s1))),  , _),  , f1),  , t1),  , (all ((uDec (bDec (_,  , (l2,  , s2))),  , _),  , f2),  , t2)) let let  inlet  inlet  inlet  inlet  in in () convForW(psi,  , (ex ((d as dec (_,  , a1),  , _),  , f1),  , t1),  , (ex ((dec (_,  , a2),  , _),  , f2),  , t2)) let let  inlet  inlet  inlet  inlet  inlet  inlet  inlet  in in () convForW(psi,  , (ex ((d as bDec (name,  , (l1,  , s1)),  , _),  , f1),  , t1),  , (ex ((bDec (_,  , (l2,  , s2)),  , _),  , f2),  , t2)) let let  inlet  inlet  inlet  inlet  inlet  in in () convForW(psi,  , (and (f1,  , f1'),  , t1),  , (and (f2,  , f2'),  , t2)) let let  inlet  in in () convForW(psi,  , (all ((d as pDec (_,  , f1,  , _,  , _),  , _),  , f1'),  , t1),  , (all ((pDec (_,  , f2,  , _,  , _),  , _),  , f2'),  , t2)) let let  inlet  inlet  in in () convForW(psi,  , (world (w1,  , f1),  , t1),  , (world (w2,  , f2),  , t2)) let let  in(* also check that both worlds are equal -- cs Mon Apr 21 01:28:01 2003 *)
 in () convForW_ raise (error "Typecheck error") convSub(g,  , shift k1,  , shift k2,  , g') if k1 = k2 then () else raise (error "Sub not equivalent") convSub(g,  , shift k,  , s2 as dot _,  , g') convSub (g,  , dot (idx (k + 1),  , shift (k + 1)),  , s2,  , g') convSub(g,  , s1 as dot _,  , shift k,  , g') convSub (g,  , s1,  , dot (idx (k + 1),  , shift (k + 1)),  , g') convSub(g,  , dot (idx k1,  , s1),  , dot (idx k2,  , s2),  , decl (g',  , _)) if k1 = k2(* For s1==s2, the variables in s1 and s2 must refer to the same cell in the context -- Yu Liao *)
 then convSub (g,  , s1,  , s2,  , g') else raise (error "Sub not equivalent") convSub(g,  , dot (exp m1,  , s1),  , dot (exp m2,  , s2),  , decl (g',  , uDec (dec (_,  , a)))) let let  in(* checkConv doesn't need context G?? -- Yu Liao *)
let  in in convSub (g,  , s1,  , s2,  , g') convSub(g,  , dot (block (bidx v1),  , s1),  , dot (block (bidx v2),  , s2),  , decl (g',  , uDec (bDec (_,  , (l,  , s))))) let let  inlet  inlet  inlet  inlet  inlet  inlet  in in convSub (g,  , s1,  , s2,  , g') convSub(g,  , dot (prg p1,  , s1),  , dot (prg p2,  , s2),  , decl (g',  , pDec (_,  , f,  , _,  , _))) let let  inlet  inlet  in in convSub (g,  , s1,  , s2,  , g') convSub(g,  , dot (idx k1,  , s1),  , dot (exp m2,  , s2),  , decl (g',  , uDec (dec (_,  , a)))) let let  inlet  in in convSub (g,  , s1,  , s2,  , g') convSub(g,  , dot (exp m1,  , s1),  , dot (idx k2,  , s2),  , decl (g',  , uDec (dec (_,  , a)))) let let  inlet  in in convSub (g,  , s1,  , s2,  , g') convSub(g,  , dot (idx k1,  , s1),  , dot (prg p2,  , s2),  , decl (g',  , pDec (_,  , f,  , _,  , _))) let let  inlet  in in convSub (g,  , s1,  , s2,  , g') convSub(g,  , dot (prg p1,  , s1),  , dot (idx k2,  , s2),  , decl (g',  , pDec (_,  , f,  , _,  , _))) let let  inlet  in in convSub (g,  , s1,  , s2,  , g') convValue(g,  , p1,  , p2,  , f) () checkFor(psi,  , (true,  , _)) () checkFor(psi,  , (all ((d as pDec (_,  , f1,  , _,  , _),  , _),  , f2),  , t)) (checkFor (psi,  , (f1,  , t)); checkFor (decl (psi,  , d),  , (f2,  , dot1 t))) checkFor(psi,  , (all ((d' as uDec d,  , _),  , f),  , t)) (checkDec (coerceCtx psi,  , (d,  , coerceSub t)); checkFor (decl (psi,  , d'),  , (f,  , dot1 t))) checkFor(psi,  , (ex ((d,  , _),  , f),  , t)) (checkDec (coerceCtx psi,  , (d,  , coerceSub t)); checkFor (decl (psi,  , uDec d),  , (f,  , dot1 t))) checkFor(psi,  , (and (f1,  , f2),  , t)) (checkFor (psi,  , (f1,  , t)); checkFor (psi,  , (f2,  , t))) checkFor(psi,  , (fClo (f,  , t'),  , t)) checkFor (psi,  , (f,  , comp (t',  , t))) checkFor(psi,  , (world (w,  , f),  , t)) checkFor (psi,  , (f,  , t)) checkCtx(null) () checkCtx(decl (psi,  , uDec d)) (checkCtx (psi); checkDec (coerceCtx psi,  , (d,  , id))) checkCtx(decl (psi,  , pDec (_,  , f,  , _,  , _))) (checkCtx (psi); checkFor (psi,  , (f,  , id)))(* checkSub (Psi, t, Psi') = ()

       Invariant
       If Psi |- t: Psi' then checkSub terminates with ()
       otherwise exception Error is raised
    *)
 checkSub(null,  , shift 0,  , null) () checkSub(decl (g,  , d),  , shift k,  , null) if k > 0 then checkSub (g,  , shift (k - 1),  , null) else raise (error "Sub is not well typed!") checkSub(g,  , shift k,  , g') checkSub (g,  , dot (idx (k + 1),  , shift (k + 1)),  , g') checkSub(g,  , dot (idx k,  , s'),  , decl (g',  , (uDec (dec (_,  , a))))) let let  inlet  in in if conv ((a',  , id),  , (a,  , coerceSub (s'))) then () else raise (error "Sub isn't well typed!") checkSub(g,  , dot (idx k,  , s'),  , decl (g',  , uDec (bDec (l,  , (_,  , s))))) let let  inlet  in in if (l <> l1) then raise (error "Sub isn't well typed!") else if convSub (comp (s,  , coerceSub (s')),  , s1) then () else raise (error "Sub isn't well typed!") checkSub(g,  , dot (idx k,  , s),  , decl (g',  , pDec (_,  , f',  , _,  , _))) let let  inlet  in in convFor (g,  , (f1,  , id),  , (f',  , s)) checkSub(g,  , dot (exp m,  , s),  , decl (g',  , uDec (dec (_,  , a)))) let let  in in typeCheck (coerceCtx g,  , (m,  , eClo (a,  , coerceSub (s)))) checkSub(psi,  , dot (prg p,  , t),  , decl (psi',  , pDec (_,  , f',  , _,  , _))) let let  inlet  inlet  in in checkPrg (psi,  , (p,  , (f',  , t))) checkSub(psi,  , dot (block b,  , t),  , decl (psi',  , uDec (bDec (l2,  , (c,  , s2))))) let let  inlet  in(* Psi |- t : Psi' *)
(* Psi' |- s2 : SOME variables of c *)
let  in(* Psi |- s2 : G *)
let  in in checkBlock (psi,  , (b,  , (c,  , comp (s2,  , coerceSub t)))) checkSub(psi,  , dot _,  , null) raise (error "Sub is not well typed") checkBlock(psi,  , (bidx v,  , (c2,  , s2))) let let  in in if (c1 <> c2) then raise (error "Sub isn't well typed!") else if convSub (s2,  , s1) then () else raise (error "Sub isn't well typed!") checkBlock(psi,  , (inst uL,  , (c2,  , s2))) let let  in(* Psi |- s2 : G *)
let  in in checkInst (psi,  , uL,  , (1,  , l,  , s2))(* Invariant:

      If   Psi |- s2 : Psi'    Psi' |-  Bn ... Bm
      and  Psi |- s : [cn :An ... cm:Am]
      and  Ai == Bi n<= i<=m
      then checkInst returns () otherwise an exception is raised.
   *)
 checkInst(psi,  , nil,  , (_,  , nil,  , _)) () checkInst(psi,  , u :: uL,  , (n,  , d :: l,  , s2)) let let  inlet  inlet  in in checkInst (psi,  , uL,  , (n + 1,  , l,  , dot1 s2)) isValue(var _) () isValue(pClo (lam _,  , _)) () isValue(pairExp (m,  , p)) isValue p isValue(pairBlock _) () isValue(pairPrg (p1,  , p2)) (isValue p1; isValue p2) isValueunit () isValue(rec _) () isValue(const lemma) (match (lemmaLookup lemma) with forDec _ -> raise (error "Lemma isn't a value") valDec (_,  , p,  , _) -> isValue p) isValue_ raise (error "P isn't Value!")(*  remove later!
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
let rec check(psi,  , (p,  , f)) checkPrg (psi,  , (p,  , (f,  , id)))let  inlet  inlet  inlet  inend