Opsem  Whnf WHNF    Abstract ABSTRACT    Subordinate SUBORDINATE    TomegaTypeCheck TOMEGATYPECHECK    TomegaPrint TOMEGAPRINT    Unify UNIFY     OPSEM  struct module module module module exception exception (*  local -- removed ABP 1/19/03 *)
exception (*
 matchPrg is used to see if two values can be 'unified' for
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
let rec matchPrg(psi,  , p1,  , p2) matchVal (psi,  , (p1,  , id),  , normalizePrg (p2,  , id))(* ABP -- normalizePrg invariant does not state what happens to non-free EVArs,
       and there are some embedded under PClo... *)
 matchVal(psi,  , (unit,  , _),  , unit) () matchVal(psi,  , (pairPrg (p1,  , p1'),  , t1),  , pairPrg (p2,  , p2')) (matchVal (psi,  , (p1,  , t1),  , p2); matchVal (psi,  , (p1',  , t1),  , p2')) matchVal(psi,  , (pairBlock (b1,  , p1),  , t1),  , pairBlock (b2,  , p2)) (matchVal (psi,  , (p1,  , t1),  , p2); try  with ) matchVal(psi,  , (pairExp (u1,  , p1),  , t1),  , pairExp (u2,  , p2)) (matchVal (psi,  , (p1,  , t1),  , p2); try  with ) matchVal(psi,  , (pClo (p,  , t1'),  , t1),  , pt) matchVal (psi,  , (p,  , comp (t1',  , t1)),  , pt) matchVal(psi,  , (p',  , t1),  , pClo (pClo (p,  , t2),  , t3)) matchVal (psi,  , (p',  , t1),  , pClo (p,  , comp (t2,  , t3))) matchVal(psi,  , (p',  , t1),  , pClo (eVar (_,  , r as ref nONE,  , _,  , _,  , _,  , _),  , t2)) let let  in in (* ABP -- just make sure this is right *)
r := sOME (pClo (p',  , comp (t1,  , iw))) matchVal(psi,  , (p',  , t1),  , eVar (_,  , r as ref nONE,  , _,  , _,  , _,  , _)) r := sOME (pClo (p',  , t1)) matchVal(psi,  , (v,  , t),  , eVar ((d,  , r as ref (sOME p),  , f,  , _,  , _,  , _))) matchVal (psi,  , (v,  , t),  , p) matchVal_ raise (noMatch)let rec append(g1,  , null) g1 append(g1,  , decl (g2,  , d)) decl (append (g1,  , g2),  , d)(* raisePrg is used in handling of NEW construct
   raisePrg (G, P, F) = (P', F'))

       Invariant:
       If   Psi, G |- P in F
       and  Psi |- G : blockctx
       then Psi |- P' in F'
       and  P = raise (G, P')   (using subordination)
       and  F = raise (G, F')   (using subordination)
*)
 raisePrg(psi,  , g,  , unit) unit raisePrg(psi,  , g,  , pairPrg (p1,  , p2)) let let  inlet  in in pairPrg (p1',  , p2') raisePrg(psi,  , g,  , pairExp (u,  , p)) let let  in(* this is a real time sink, it would be much better if we did not have to
      compute the type information of U,
      more thought is required
   *)
let  in(* G  |- w  : G'    *)
let  in(* G' |- iw : G     *)
let  in(* Psi0, G' |- B'' ctx *)
let  inlet  in in pairExp (u',  , p')(* evalPrg (Psi, (P, t)) = V

       Invariant:
       If   Psi' |- P :: F
       and  Psi |- t :: Psi'
       and  |- Psi ctx[block]
       and  Psi |- P :: F'
       and  Psi |- P[t] evalsto V
       and  Psi |- F[t] == F'
    *)
 evalPrg(psi,  , (unit,  , t)) unit evalPrg(psi,  , (pairExp (m,  , p),  , t)) pairExp (eClo (m,  , coerceSub t),  , evalPrg (psi,  , (p,  , t))) evalPrg(psi,  , (pairBlock (b,  , p),  , t)) pairBlock (blockSub (b,  , coerceSub t),  , evalPrg (psi,  , (p,  , t))) evalPrg(psi,  , (pairPrg (p1,  , p2),  , t)) pairPrg (evalPrg (psi,  , (p1,  , t)),  , evalPrg (psi,  , (p2,  , t))) evalPrg(psi,  , (redex (p,  , s),  , t)) evalRedex (psi,  , evalPrg (psi,  , (p,  , t)),  , (s,  , t)) evalPrg(psi,  , (var k,  , t)) (match varSub (k,  , t) with prg p -> evalPrg (psi,  , (p,  , id))) evalPrg(psi,  , (const lemma,  , t)) evalPrg (psi,  , (lemmaDef lemma,  , t)) evalPrg(psi,  , (lam (d as uDec (bDec _),  , p),  , t)) let let  in in lam (d',  , evalPrg (decl (psi,  , d'),  , (p,  , dot1 t))) evalPrg(psi,  , (lam (d,  , p),  , t)) lam (decSub (d,  , t),  , pClo (p,  , dot1 t)) evalPrg(psi,  , (p' as rec (d,  , p),  , t)) evalPrg (psi,  , (p,  , dot (prg (pClo (p',  , t)),  , t))) evalPrg(psi,  , (pClo (p,  , t'),  , t)) evalPrg (psi,  , (p,  , comp (t',  , t))) evalPrg(psi,  , (case (cases o),  , t')) match (psi,  , t',  , cases (rev o)) evalPrg(psi,  , (eVar (d,  , r as ref (sOME p),  , f,  , _,  , _,  , _),  , t)) evalPrg (psi,  , (p,  , t)) evalPrg(psi,  , (let (d,  , p1,  , p2),  , t)) let let  inlet  in in v' evalPrg(psi,  , (new (lam (d,  , p)),  , t)) let let  inlet  inlet  in(* unnecessary naming, remove later --cs *)
let  inlet  inlet  inlet  in in newP evalPrg(psi,  , (box (w,  , p),  , t)) evalPrg (psi,  , (p,  , t)) evalPrg(psi,  , (choose p,  , t)) let (* This function was imported from cover.fun   -- cs Thu Mar 20 11:47:06 2003 *)
(* substtospine' (s, G, T) = S @ T
                If   G' |- s : G
                then G' |- S : {{G}} a >> a  for arbitrary a
                    {{G}} erases void declarations in G
              *)
let rec substToSpine'(shift (n),  , null,  , t) t substToSpine'(shift (n),  , g as decl _,  , t) substToSpine' (dot (idx (n + 1),  , shift (n + 1)),  , g,  , t) substToSpine'(dot (exp (u),  , s),  , decl (g,  , v),  , t) substToSpine' (s,  , g,  , appExp (u,  , t)) substToSpine'(dot (idx (n),  , s),  , decl (g,  , dec (_,  , v)),  , t) let let  in in substToSpine' (s,  , g,  , appExp (eClo us,  , t))let rec choose(k,  , null) raise (abort) choose(k,  , decl (psi',  , pDec _)) choose (k + 1,  , psi') choose(k,  , decl (psi',  , uDec (dec _))) choose (k + 1,  , psi') choose(k,  , decl (psi',  , uDec (bDec (_,  , (l1,  , s1))))) let let  inlet  in in try  with  in choose (1,  , psi)(* other cases should not occur -cs *)
(* match is used to handle Case statements
  match (Psi, t1, O) = V

       Invariant:
       If   Psi |- t1 :: Psi''
       and  Psi'' |- O :: F
       and  |- Psi ctx[block]
       then if t1 matches O then Psi |- t ~ O evalPrgs to W
            otherwise exception NoMatch is raised.
    *)
 match(psi,  , t1,  , cases ((psi',  , t2,  , p) :: c)) let (* val I.Null = Psi *)
let  in(* Psi |- t : Psi' *)
(* Psi' |- t2 . shift(k) : Psi'' *)
let  in in (* Note that since we are missing the shift(k), it is possible
           * that t' has extra DOTs in there that weren't removed *)
try  with  match(psi,  , t1,  , cases (nil)) raise (abort)(* What do you want to do if it doesn't match anything *)
(* can't happen when total function - ABP *)
(* | match (Psi, t1, T.Cases Nil) = raise Domain  *)
(* createVarSub (Psi, Psi') = t

       Invariant:
       If   |- Psi ctx[block]
       and  |- Psi' ctx
       then Psi |- t :: Psi'
    *)
 createVarSub(psi,  , null) shift (ctxLength (psi)) createVarSub(psi,  , psi'' as decl (psi',  , pDec (name,  , f,  , nONE,  , nONE))) let let  inlet  in in t' createVarSub(psi,  , decl (psi',  , uDec (dec (name,  , v)))) let let  in in dot (exp (eVar (ref nONE,  , coerceCtx psi,  , eClo (v,  , coerceSub t),  , ref [])),  , t) createVarSub(psi,  , decl (psi',  , uDec (bDec (name,  , (cid,  , s))))) let let  in in dot (block (lVar (ref nONE,  , id,  , (cid,  , comp (s,  , coerceSub t)))),  , t)(* matchSub (t1, t2) = ()

       Invariant:
       If   Psi  |- t1 :: Psi'
       and  Psi  |- t2 :: Psi'
       and  Psi  |- t1 == t2 :: Psi'
       and  |- Psi ctx [block]
       then function returns ()
            otherwise exception NoMatch is raised
    *)
 matchSub(psi,  , _,  , shift _) () matchSub(psi,  , shift n,  , t as dot _) matchSub (psi,  , dot (idx (n + 1),  , shift (n + 1)),  , t) matchSub(psi,  , dot (exp u1,  , t1),  , dot (exp u2,  , t2)) (matchSub (psi,  , t1,  , t2); try  with ) matchSub(psi,  , dot (exp u1,  , t1),  , dot (idx k,  , t2)) (matchSub (psi,  , t1,  , t2); try  with ) matchSub(psi,  , dot (idx k,  , t1),  , dot (exp u2,  , t2)) (matchSub (psi,  , t1,  , t2); try  with ) matchSub(psi,  , dot (prg p1,  , t1),  , dot (prg p2,  , t2)) (matchSub (psi,  , t1,  , t2); matchPrg (psi,  , p1,  , p2)) matchSub(psi,  , dot (prg p1,  , t1),  , dot (idx k,  , t2)) (matchSub (psi,  , t1,  , t2); matchPrg (psi,  , p1,  , var k)) matchSub(psi,  , dot (idx k,  , t1),  , dot (prg p2,  , t2)) (matchSub (psi,  , t1,  , t2); matchPrg (psi,  , var k,  , p2)) matchSub(psi,  , dot (idx k1,  , t1),  , dot (idx k2,  , t2)) (if k1 = k2 then matchSub (psi,  , t1,  , t2) else raise (noMatch)) matchSub(psi,  , dot (idx k,  , t1),  , dot (block (lVar (r,  , s1,  , (c,  , s2))),  , t2)) let let  inlet  in in matchSub (psi,  , t1,  , t2) matchSub(psi,  , dot (block (b),  , t1),  , dot (block (lVar (r,  , s1,  , (c,  , s2))),  , t2)) let let  inlet  in in matchSub (psi,  , t1,  , t2)(* evalRedex (Psi, V, (S, t)) = V'

       Invariant:
       If   Psi  |- V :: F1
       and  Psi' |- S :: F2 > F3
       and  Psi  |- t :: Psi'
       and  Psi' |- F1 == F2[t]
       and  |- Psi ctx[block]
       and  Psi |- P :: F'
       and  Psi |- V . (S[t]) evalsto V''
       then Psi |- V' == V'' : F3[t]
    *)
 evalRedex(psi,  , v,  , (nil,  , _)) v evalRedex(psi,  , v,  , (sClo (s,  , t1),  , t2)) evalRedex (psi,  , v,  , (s,  , comp (t1,  , t2))) evalRedex(psi,  , lam (uDec (dec (_,  , a)),  , p'),  , (appExp (u,  , s),  , t)) let let  in in evalRedex (psi,  , v,  , (s,  , t)) evalRedex(psi,  , lam (uDec _,  , p'),  , (appBlock (b,  , s),  , t)) evalRedex (psi,  , evalPrg (psi,  , (p',  , dot (block (blockSub (b,  , coerceSub t)),  , id))),  , (s,  , t)) evalRedex(psi,  , lam (pDec _,  , p'),  , (appPrg (p,  , s),  , t)) let let  inlet  in in evalRedex (psi,  , v',  , (s,  , t))(* topLevel (Psi, d, (P, t))

       Invariant:
       Psi |- t : Psi'
       Psi' |- P :: F
       d = | Psi' |

    *)
let rec topLevel(psi,  , d,  , (unit,  , t)) () topLevel(psi,  , d,  , (let (d',  , p1,  , case cs),  , t)) let (* printLF (G, s, G') k = ()
             Invariant:
             G |- s : G'
          *)
let rec printLF(_,  , _,  , _)0 () printLF(g,  , dot (exp u,  , s'),  , decl (g',  , dec (sOME name,  , v)))k let let  in in print ("def " ^ name ^ " = " ^ (expToString (g,  , u)) ^ " : " ^ (expToString (g,  , eClo (v,  , s'))) ^ "\n")let rec match(psi,  , t1,  , cases ((psi',  , t2,  , p) :: c)) let let  in(* Psi |- t : Psi' *)
(* Psi' |- t2 . shift(k) : Psi'' *)
let  inlet  inlet  inlet  in(* Psi |- t'' : Psi' *)
let  in in topLevel (psi,  , m,  , (p,  , t''))let  inlet  in in v' topLevel(psi,  , d,  , (let (d,  , lam (d' as uDec (bDec (sOME name,  , (cid,  , s))),  , p1),  , p2),  , t)) let let  inlet  inlet  in in () topLevel(psi,  , d,  , (let (d,  , p1,  , p2),  , t)) let let  inlet  inlet  inlet  in in v'(* in -- removed local *)
let  inlet  in(* end -- removed local *)
end