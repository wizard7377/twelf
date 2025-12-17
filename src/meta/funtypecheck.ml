FunTypeCheck  StateSyn' STATESYN    Abstract ABSTRACT    TypeCheck TYPECHECK    Conv CONV    Whnf WHNF    Print PRINT    Subordinate SUBORDINATE    Weaken WEAKEN    FunPrint FUNPRINT     FUNTYPECHECK  struct (*! structure FunSyn = FunSyn' !*)
module exception module module module (* conv ((G, s), (G', s')) = B

       Invariant:
       B iff G [s]  == G' [s']
       Might migrate in to conv module  --cs
    *)
let rec conv(gs,  , gs') let exception let rec conv((null,  , s),  , (null,  , s')) (s,  , s') conv((decl (g,  , dec (_,  , v)),  , s),  , (decl (g',  , dec (_,  , v')),  , s')) let let  inlet  in in if conv ((v,  , s1),  , (v',  , s1')) then ps else raise (conv) conv_ raise (conv) in try  with (* extend (G, L) = G'

       Invariant:
       If   G : 'a ctx
       and  L : 'a list
       then G' = G, L : 'a ctx
    *)
let rec extend(g,  , nil) g extend(g,  , d :: l) extend (decl (g,  , d),  , l)(* validBlock (Psi, k, (l : G)) = ()

       Invariant:
       If   |- Psi ctx
       and  |- k is a debruijn index (for LF context)
       and  |- l label
       and  |- G LFctx
       then validBlock terminates with ()
       iff  Psi = Psi1, l': (x1:A1 .. xn:An), Psi2
       and  l = l'
       and  Psi(k) = x1
       and  G == x1:A1 .. xn:An
    *)
let rec validBlock(psi,  , k,  , (l,  , g)) let let rec skipBlock(null,  , k) k skipBlock(decl (g',  , _),  , k) skipBlock (g',  , k - 1)let rec validBlock'(decl (psi,  , block (ctxBlock (l',  , g'))),  , 0) if (l' = l) && conv ((g,  , id),  , (g',  , id)) then () else raise (error "Typecheck Error: Not a valid block") validBlock'(decl (psi,  , prim _),  , 0) raise (error "Typecheck Error: Not a valid block") validBlock'(null,  , k) raise (error "Typecheck Error: Not a valid block") validBlock'(decl (psi,  , block (ctxBlock (l',  , g'))),  , k) validBlock' (psi,  , skipBlock (g',  , k)) validBlock'(decl (psi,  , prim (d)),  , k) validBlock' (psi,  , k - 1) in validBlock' (psi,  , k)(* raiseSub (l:G, Psi') = s'

       Invariant:
       If   |- Psi ctx
       and  Psi |- l:G ctx
       and  Psi, l:G |- Psi' ctx
       then Psi, {G} Psi', l:G|- s' : Psi, l:G, Psi'
    *)
let rec raiseSub(g,  , psi') let let  inlet  inlet rec args(0,  , a,  , s) s args(n',  , a,  , s) let let  in in if belowEq (targetFam v,  , a) then args (n' - 1,  , a,  , app (root (bVar n',  , nil),  , s)) else args (n' - 1,  , a,  , s)let rec termm' let let  in in exp (root (bVar (n + m'),  , args (n,  , targetFam (v),  , nil)))let rec raiseSub''(0,  , s) s raiseSub''(m',  , s) raiseSub'' (m' - 1,  , dot (term m',  , s))let rec raiseSub'(0,  , s) raiseSub'' (m,  , s) raiseSub'(n',  , s) raiseSub' (n' - 1,  , dot (idx n',  , s)) in raiseSub' (n,  , shift (n + m))(* raiseType (l:G, L) = L'

       Invariant:
       L contains no parameter block declarations
       Each x:A in L is mapped xto  x:{G}A in L'
       L' preserves the order of L
    *)
let rec raiseType(ctxBlock (l,  , g),  , psi') let let rec raiseType''(null,  , vn,  , a) vn raiseType''(decl (g',  , d as dec (_,  , v')),  , vn,  , a) if belowEq (targetFam v',  , a) then raiseType'' (g',  , piDepend ((d,  , maybe),  , vn),  , a) else raiseType'' (g',  , strengthenExp (vn,  , shift),  , a)let rec raiseType'(psi1,  , nil) nil raiseType'(psi1,  , prim (d as dec (x,  , v)) :: psi1') let let  inlet  inlet  inlet  in in prim (d') :: (raiseType' (decl (psi1,  , d),  , psi1'))(* no case of F.Block by invariant *)
 in raiseType' (null,  , psi')(* raiseM (B, L) = L'

       Invariant
       Each xx in F in L is mapped to xx in PI B. F in L'
       L' preserves the order of L
    *)
let rec raiseM(b,  , nil) nil raiseM(b,  , mDec (xx,  , f) :: l) mDec (xx,  , all (block b,  , f)) :: raiseM (b,  , l)(* psub (k, Phi, s) = s'

       Invariant:
       If   |- Phi ctx
       and  |- Psi ctx
       and  Psi = Psi1, l': (x1:A1 .. xn:An), Psi2
       and  Psi (k) = x1
       and  | Phi | = n
       and  s = k-i ... k. id   for i <=n
       then s' = k-n . ... k . id
    *)
let rec psub(k,  , null,  , s) s psub(k,  , decl (g,  , _),  , s) psub (k - 1,  , g,  , dot (idx k,  , s))let rec deltaSub(null,  , s) null deltaSub(decl (delta,  , dD),  , s) decl (deltaSub (delta,  , s),  , mdecSub (dD,  , s))let rec shiftdelta deltaSub (delta,  , shift)let rec shifts(null,  , delta) delta shifts(decl (g,  , _),  , delta) shifts (g,  , shift delta)let rec shiftBlock(ctxBlock (_,  , g),  , delta) shifts (g,  , delta)let rec shiftSub(null,  , s) s shiftSub(decl (g,  , _),  , s) shiftSub (g,  , comp (shift,  , s))let rec shiftSubBlock(ctxBlock (_,  , g),  , s) shiftSub (g,  , s)(* check (Psi, Delta, P, (F, s)) = ()

       Invariant:
       If   Psi'' |- F formula
       and  Psi |- s : Psi''
       and  Psi |- Delta mctx
        returns () if there exists a F',
              s.t. Psi, Delta |- P  : F'
              and  Psi |- F' = F[s] formula
       otherwise Error is raised
    *)
let rec check(psi,  , delta,  , unit,  , (true,  , _)) () check(psi,  , delta,  , rec (dD,  , p),  , f) (check (psi,  , decl (delta,  , dD),  , p,  , f)) check(psi,  , delta,  , lam (lD as prim (dec (_,  , v)),  , p),  , (all (prim (dec (_,  , v')),  , f'),  , s')) if (conv ((v,  , id),  , (v',  , s'))) then check (decl (psi,  , lD),  , shift delta,  , p,  , (f',  , dot1 s')) else raise (error "Typecheck Error: Primitive Abstraction") check(psi,  , delta,  , lam (lD as block (b as ctxBlock (l,  , g)),  , p),  , (all (block (ctxBlock (l',  , g')),  , f'),  , s')) (if (l = l' && conv ((g,  , id),  , (g',  , s'))) then check (decl (psi,  , lD),  , shiftBlock (b,  , delta),  , p,  , (f',  , dot1n (g,  , s'))) else raise (error "Typecheck Error: Block Abstraction")) check(psi,  , delta,  , inx (m,  , p),  , (ex (dec (_,  , v'),  , f'),  , s')) (typeCheck (makectx psi,  , (m,  , (eClo (v',  , s')))); check (psi,  , delta,  , p,  , (f',  , dot (exp (m),  , s')))) check(psi,  , delta,  , case (opts o),  , (f',  , s')) checkOpts (psi,  , delta,  , o,  , (f',  , s')) check(psi,  , delta,  , pair (p1,  , p2),  , (and (f1',  , f2'),  , s')) (check (psi,  , delta,  , p1,  , (f1',  , s')); check (psi,  , delta,  , p2,  , (f2',  , s'))) check(psi,  , delta,  , let (ds,  , p),  , (f',  , s')) let let  in in check (extend (psi,  , psi'),  , extend (delta,  , delta'),  , p,  , (f',  , comp (s',  , s''))) check_ raise (error "Typecheck Error: Term not well-typed") infer(delta,  , kk) (ctxLookup (delta,  , kk),  , id)(* assume (Psi, Delta, Ds) = (Psi', Delta', s')

       Invariant:
       If   |- Psi context
       and  Psi |- Delta assumptions
       and  Psi, Delta |- Decs declarations
       then |- Psi, Psi' context
       and  Psi, Psi' |- Delta, Delta' assumptions
       and  Psi, Psi' |- s' = ^|Psi'| : Psi
    *)
 assume(psi,  , delta,  , empty) (nil,  , nil,  , id) assume(psi,  , delta,  , split (kk,  , ds)) (match infer (delta,  , kk) with (mDec (name,  , ex (d,  , f)),  , s) -> let let  inlet  inlet  in in (lD :: psi',  , mdecSub (dD,  , s') :: delta',  , comp (shift,  , s')) _ -> raise (error "Typecheck Error: Declaration")) assume(psi,  , delta,  , new (b,  , ds)) let (* check B valid context block       <-------------- omission *)
let  inlet  in in (raiseType (b,  , psi'),  , raiseM (b,  , delta'),  , s') assume(psi,  , delta,  , app ((kk,  , u),  , ds)) (match infer (delta,  , kk) with (mDec (name,  , all (prim (dec (_,  , v)),  , f)),  , s) -> let let  inlet  inlet  in in (psi',  , mdecSub (dD,  , s') :: delta',  , s') (mDec (name,  , f),  , s) -> raise (error ("Typecheck Error: Declaration App" ^ (forToString (null,  , f) ["x"])))) assume(psi,  , delta,  , pApp ((kk,  , k),  , ds)) (match infer (delta,  , kk) with (mDec (name,  , all (block (ctxBlock (l,  , g)),  , f)),  , s) -> let let  inlet  inlet  in in (psi',  , mdecSub (dD,  , s') :: delta',  , s') _ -> raise (error "Typecheck Error: Declaration PApp")) assume(psi,  , delta,  , left (kk,  , ds)) (match infer (delta,  , kk) with (mDec (name,  , and (f1,  , f2)),  , s) -> let let  inlet  in in (psi',  , mdecSub (dD,  , s') :: delta',  , s') _ -> raise (error "Typecheck Error: Declaration Left")) assume(psi,  , delta,  , right (kk,  , ds)) (match infer (delta,  , kk) with (mDec (name,  , and (f1,  , f2)),  , s) -> let let  inlet  in in (psi',  , mdecSub (dD,  , s') :: delta',  , s') _ -> raise (error "Typecheck Error: Declaration Left")) assume(psi,  , delta,  , lemma (cc,  , ds)) let let  inlet  inlet  inlet  in in (psi',  , mdecSub (dD,  , s') :: delta',  , s')(* checkSub (Psi1, s, Psi2) = ()

       Invariant:
       The function terminates
       iff  Psi1 |- s : Psi2
    *)
 checkSub(null,  , shift 0,  , null) () checkSub(decl (psi,  , prim d),  , shift k,  , null) if k > 0 then checkSub (psi,  , shift (k - 1),  , null) else raise (error "Substitution not well-typed") checkSub(decl (psi,  , block (ctxBlock (_,  , g))),  , shift k,  , null) let let  in in if k >= g then checkSub (psi,  , shift (k - g),  , null) else raise (error "Substitution not well-typed") checkSub(psi',  , shift k,  , psi) checkSub (psi',  , dot (idx (k + 1),  , shift (k + 1)),  , psi) checkSub(psi',  , dot (idx k,  , s'),  , decl (psi,  , prim (dec (_,  , v2)))) let let  inlet  in in if conv ((v1,  , id),  , (v2,  , s')) then checkSub (psi',  , s',  , psi) else raise (error ("Substitution not well-typed \n  found: " ^ expToString (g',  , v1) ^ "\n  expected: " ^ expToString (g',  , eClo (v2,  , s')))) checkSub(psi',  , dot (exp (u),  , s'),  , decl (psi,  , prim (dec (_,  , v2)))) let let  inlet  in in checkSub (psi',  , s',  , psi) checkSub(psi',  , s as dot (idx k,  , _),  , decl (psi,  , block (ctxBlock (l1,  , g)))) let let  in(* check that l1 = l2     <----------------------- omission *)
(* checkSub' ((G', w), s, G, m) = ()
          *)
let rec checkSub'((null,  , w1),  , s1,  , null,  , _) s1 checkSub'((decl (g',  , dec (_,  , v')),  , w1),  , dot (idx k',  , s1),  , decl (g,  , dec (_,  , v)),  , m) if k' = m then if conv ((v',  , w1),  , (v,  , s1)) then checkSub' ((g',  , comp (w1,  , shift)),  , s1,  , g,  , m + 1) else raise (error "ContextBlock assignment not well-typed") else raise (error "ContextBlock assignment out of order") in checkSub (psi',  , checkSub' ((g',  , w),  , s,  , g,  , k),  , psi)(* checkOpts (Psi, Delta, (O, s) *)
 checkOpts(psi,  , delta,  , nil,  , _) () checkOpts(psi,  , delta,  , (psi',  , t,  , p) :: o,  , (f',  , s')) (checkSub (psi',  , t,  , psi); check (psi',  , deltaSub (delta,  , t),  , p,  , (f',  , comp (s',  , t))); (* [Psi' strict in  t] <------------------------- omission*)
checkOpts (psi,  , delta,  , o,  , (f',  , s')))let rec checkRec(p,  , t) check (null,  , null,  , p,  , (t,  , id))let rec isFor(g,  , all (prim d,  , f)) (try  with ) isFor(g,  , all (block (ctxBlock (_,  , g1)),  , f)) isForBlock (g,  , ctxToList g1,  , f) isFor(g,  , ex (d,  , f)) (try  with ) isFor(g,  , true) () isFor(g,  , and (f1,  , f2)) (isFor (g,  , f1); isFor (g,  , f2)) isForBlock(g,  , nil,  , f) isFor (g,  , f) isForBlock(g,  , d :: g1,  , f) isForBlock (decl (g,  , d),  , g1,  , f)let rec checkTags'(v,  , ex _) () checkTags'(pi (_,  , v),  , all (_,  , f)) checkTags' (v,  , f) checkTags'_ raise (domain)let rec checkTags(null,  , null) () checkTags(decl (g,  , dec (_,  , v)),  , decl (b,  , t)) (checkTags (g,  , b); match t with lemma (_) -> () _ -> ())(* isState (S) = ()

       Invariant:

       Side effect:
       If it doesn't hold that |- S state, then exception Error is raised

       Remark: Function is only partially implemented
    *)
let rec isState(state (n,  , (g,  , b),  , (iH,  , oH),  , d,  , o,  , h,  , f)) (typeCheckCtx g; checkTags (g,  , b); if (not (closedCtx g)) then raise (error "State context not closed!") else (); map (fun (n',  , f') -> (isFor (g,  , f')(* ;          TextIO.print ("Checked: " ^ (FunPrint.Formatter.makestring_fmt (FunPrint.formatForBare (G, F'))) ^ "\n") *)
)) h; (* n' is not checked for consistency   --cs *)
isFor (g,  , f))let  inlet  inlet  inlet  inend