Reduces  Global GLOBAL    Whnf WHNF    Names NAMES    Index INDEX    Subordinate SUBORDINATE    Formatter FORMATTER    Print PRINT    Print Formatter  Formatter   Order ORDER    Checking CHECKING    Checking Order  Order   Origins ORIGINS     REDUCES  struct (*! structure IntSyn = IntSyn' !*)
exception module module module module module module exception let rec error(c,  , occ,  , msg) (match originLookup c with (fileName,  , nONE) -> raise (error (fileName ^ ":" ^ msg)) (fileName,  , sOME occDec) -> raise (error (wrapLoc' (loc (fileName,  , occToRegionDec occDec occ),  , linesInfoLookup (fileName),  , msg))))let rec concat(g',  , null) g' concat(g',  , decl (g,  , d)) decl (concat (g',  , g),  , d)(*--------------------------------------------------------------------*)
(* Printing *)
let rec fmtOrder(g,  , o) let let rec fmtOrder'(arg (us as (u,  , s),  , vs as (v,  , s'))) hbox [string "("; formatExp (g,  , eClo us); string ")"] fmtOrder'(lex l) hbox [string "{"; hOVbox0 1 0 1 (fmtOrders l); string "}"] fmtOrder'(simul l) hbox [string "["; hOVbox0 1 0 1 (fmtOrders l); string "]"] fmtOrders[] [] fmtOrders(o :: []) fmtOrder' o :: [] fmtOrders(o :: l) fmtOrder' o :: break :: fmtOrders l in fmtOrder' olet rec fmtComparison(g,  , o,  , comp,  , o') hOVbox0 1 0 1 [fmtOrder (g,  , o); break; string comp; break; fmtOrder (g,  , o')]let rec fmtPredicate(g,  , less (o,  , o')) fmtComparison (g,  , o,  , "<",  , o') fmtPredicate(g,  , leq (o,  , o')) fmtComparison (g,  , o,  , "<=",  , o') fmtPredicate(g,  , eq (o,  , o')) fmtComparison (g,  , o,  , "=",  , o') fmtPredicate(g,  , pi (d,  , p)) hbox [string "Pi "; fmtPredicate (decl (g,  , d),  , p)]let rec rlistToString'(g,  , nil) "" rlistToString'(g,  , [p]) makestring_fmt (fmtPredicate (g,  , p)) rlistToString'(g,  , (p :: rl)) makestring_fmt (fmtPredicate (g,  , p)) ^ " ," ^ rlistToString' (g,  , rl)let rec rlistToString(g,  , rl) rlistToString' (ctxName g,  , rl)let rec orderToString(g,  , p) makestring_fmt (fmtPredicate (ctxName g,  , p))(*--------------------------------------------------------------------*)
(* select (c, (S, s)) = P

      select parameters according to termination order

      Invariant:
      If   . |- c : V   G |- s : G'    G' |- S : V > type
      and  V = {x1:V1} ... {xn:Vn} type.
      then P = U1[s1] .. Un[sn] is parameter select of S[s] according to sel (c)
      and  G |- si : Gi  Gi |- Ui : Vi
      and  G |- Vi[s]  == V[si] : type   forall 1<=i<=n
    *)
let rec select(c,  , (s,  , s)) let let  inlet  inlet rec select''(n,  , (ss',  , vs'')) select''W (n,  , (ss',  , whnf vs'')) select''W(1,  , ((app (u',  , s'),  , s'),  , (pi ((dec (_,  , v''),  , _),  , _),  , s''))) ((u',  , s'),  , (v'',  , s'')) select''W(n,  , ((sClo (s',  , s1'),  , s2'),  , vs'')) select''W (n,  , ((s',  , comp (s1',  , s2')),  , vs'')) select''W(n,  , ((app (u',  , s'),  , s'),  , (pi ((dec (_,  , v1''),  , _),  , v2''),  , s''))) select'' (n - 1,  , ((s',  , s'),  , (v2'',  , dot (exp (eClo (u',  , s')),  , s''))))let rec select'(arg n) arg (select'' (n,  , ((s,  , s),  , vid))) select'(lex l) lex (map select' l) select'(simul l) simul (map select' l) in select' (selLookup c)let rec selectOcc(c,  , (s,  , s),  , occ) try  with (* selectROrder (c, (S, s)) = P

       select parameters according to reduction order

       Invariant:
       If   . |- c : V   G |- s : G'    G' |- S : V > type
       and  V = {x1:V1} ... {xn:Vn} type.
       then P = U1[s1] .. Un[sn] is parameter select of S[s] according to sel (c)
       and  G |- si : Gi  Gi |- Ui : Vi
       and  G |- Vi[s]  == V[si] : type   forall 1<=i<=n
    *)
let rec selectROrder(c,  , (s,  , s)) let let  inlet rec select''(n,  , (ss',  , vs'')) select''W (n,  , (ss',  , whnf vs'')) select''W(1,  , ((app (u',  , s'),  , s'),  , (pi ((dec (_,  , v''),  , _),  , _),  , s''))) ((u',  , s'),  , (v'',  , s'')) select''W(n,  , ((sClo (s',  , s1'),  , s2'),  , vs'')) select''W (n,  , ((s',  , comp (s1',  , s2')),  , vs'')) select''W(n,  , ((app (u',  , s'),  , s'),  , (pi ((dec (_,  , v1''),  , _),  , v2''),  , s''))) select'' (n - 1,  , ((s',  , s'),  , (v2'',  , dot (exp (eClo (u',  , s')),  , s''))))let rec select'(arg n) arg (select'' (n,  , ((s,  , s),  , vid))) select'(lex l) lex (map select' l) select'(simul l) simul (map select' l)let rec selectP(less (o1,  , o2)) less (select' o1,  , select' o2) selectP(leq (o1,  , o2)) leq (select' o1,  , select' o2) selectP(eq (o1,  , o2)) eq (select' o1,  , select' o2) in try  with (*--------------------------------------------------------------*)
(* abstractRO (G, D, RO) = Pi D. RO
       Invariant:

       If  G, D |- RO
       then  G |- Pi D . RO

    *)
let rec abstractRO(g,  , d,  , o) pi (d,  , o)(* getROrder (G, Q, (V, s)) = O
       If G: Q
       and  G |- s : G1    and   G1 |- V : L
       then O is the reduction order associated to V[s]
       and  G |- O

     *)
let rec getROrder(g,  , q,  , vs,  , occ) getROrderW (g,  , q,  , whnf vs,  , occ) getROrderW(g,  , q,  , vs as (root (const a,  , s),  , s),  , occ) let let  inlet  in in o getROrderW(g,  , q,  , (pi ((d,  , maybe),  , v),  , s),  , occ) let let  in in match o with nONE -> nONE sOME (o') -> sOME (abstractRO (g,  , decSub (d,  , s),  , o')) getROrderW(g,  , q,  , (pi ((d as dec (_,  , v1),  , no),  , v2),  , s),  , occ) let let  in in match o with nONE -> nONE sOME (o') -> sOME (o') getROrderW(g,  , q,  , vs as (root (def a,  , s),  , s),  , occ) raise (error' (occ,  , "Reduction checking for defined type families not yet available:\n" ^ "Illegal use of " ^ qidToString (constQid a) ^ "."))(*--------------------------------------------------------------------*)
(* Termination Checker *)
(* checkGoal (G0, Q0, Rl, (V, s), (V', s'), occ) = ()

       Invariant:
       If   G0 : Q0
       and  G0 |- s : G1     and   G1 |- V : L     (V, s) in whnf
       and  V[s], V'[s'] does not contain Skolem constants
       and  G0 |- s' : G2    and   G2 |- V' : L'   (V', s') in whnf
       and  V' = a' @ S'
       and  G |- L = L'
       and  V[s] < V'[s']  (< termination ordering)
         then ()
       else Error is raised.
    *)
let rec checkGoal(g0,  , q0,  , rl,  , vs,  , vs',  , occ) checkGoalW (g0,  , q0,  , rl,  , whnf vs,  , vs',  , occ) checkGoalW(g0,  , q0,  , rl,  , (pi ((d as dec (_,  , v1),  , no),  , v2),  , s),  , vs',  , occ) (checkClause ((g0,  , q0,  , rl),  , null,  , null,  , (v1,  , s),  , label occ); checkGoal (g0,  , q0,  , rl,  , (v2,  , comp (invShift,  , s)),  , vs',  , body occ)) checkGoalW(g0,  , q0,  , rl,  , (pi ((d,  , maybe),  , v),  , s),  , (v',  , s'),  , occ) checkGoal (decl (g0,  , decLUName (g0,  , decSub (d,  , s))),  , decl (q0,  , all),  , shiftRCtx rl (fun s -> comp (s,  , shift)),  , (v,  , dot1 s),  , (v',  , comp (s',  , shift)),  , body occ) checkGoalW(g0,  , q0,  , rl,  , vs as (root (const a,  , s),  , s),  , vs' as (root (const a',  , s'),  , s'),  , occ) let let rec lookup(empty,  , f) empty lookup(a's as lE (a,  , a's'),  , f) if (f a) then a's else lookup (a's',  , f) lookup(a's as lT (a,  , a's'),  , f) if (f a) then a's else lookup (a's',  , f)let  in(* only if a terminates? *)
let  in(* always succeeds? -fp *)
let  in(* always succeeds? -fp *)
 in (match lookup (a's,  , fun x' -> x' = a') with empty -> () lE _ -> (if (! chatter) > 4 then (print ("Verifying termination order:\n"); print (rlistToString (g0,  , rl)); print (" ---> " ^ orderToString (g0,  , leq (p,  , p')) ^ "\n")) else (); if deduce (g0,  , q0,  , rl,  , leq (p,  , p')) then () else raise (error' (occ,  , "Termination violation:\n" ^ rlistToString (g0,  , rl) ^ " ---> " ^ orderToString (g0,  , leq (p,  , p'))))) lT _ -> (if (! chatter) > 4 then (print "Verifying termination order:\n"; print (rlistToString (g0,  , rl) ^ " ---> "); print (orderToString (g0,  , less (p,  , p')) ^ "\n")) else (); if deduce (g0,  , q0,  , rl,  , less (p,  , p')) then () else raise (error' (occ,  , "Termination violation:\n" ^ rlistToString (g0,  , rl) ^ " ---> " ^ orderToString (g0,  , less (p,  , p')))))) checkGoalW(g0,  , q0,  , rl,  , vs as (root (def a,  , s),  , s),  , vs',  , occ) raise (error' (occ,  , "Reduction checking for defined type families not yet available:\n" ^ "Illegal use of " ^ qidToString (constQid a) ^ ".")) checkGoalW(g0,  , q0,  , rl,  , vs,  , vs' as (root (def a',  , s'),  , s'),  , occ) raise (error' (occ,  , "Reduction checking for defined type families not yet available:\n" ^ "Illegal use of " ^ qidToString (constQid a') ^ "."))(* checkSubgoals (G0, Q0, Rl, Vs, n, (G, Q), Vs, occ)

      if    G0 |- Q0
       and  G0 |- s : G1    and   G1 |- V : L
       and  V[s] does not contain any skolem constants
       and  Rl is a list of reduction propositions
       and  G0 |- Rl
       and  G0 |- V[s]
       and  G0 = G0', G' where G' <= G
       and  n = |G'| - |G|
       and  G0 |- G[^n]
       and  G |- Q
     and
       V[s] satisfies the associated termination order

     *)
 checkSubgoals(g0,  , q0,  , rl,  , vs,  , n,  , (decl (g,  , d as dec (_,  , v')),  , decl (q,  , and (occ)))) let let  inlet  inlet  in in checkSubgoals (g0,  , q0,  , rl',  , vs,  , n + 1,  , (g,  , q)) checkSubgoals(g0,  , q0,  , rl,  , vs,  , n,  , (decl (g,  , d),  , decl (q,  , exist))) checkSubgoals (g0,  , q0,  , rl,  , vs,  , n + 1,  , (g,  , q)) checkSubgoals(g0,  , q0,  , rl,  , vs,  , n,  , (decl (g,  , d),  , decl (q,  , all))) checkSubgoals (g0,  , q0,  , rl,  , vs,  , n + 1,  , (g,  , q)) checkSubgoals(g0,  , q0,  , rl,  , vs,  , n,  , (null,  , null)) ()(* checkClause (GQR as (G0, Q0, Rl), G, Q, Vs, occ)

      if   G0, G |- Q0, Q
       and  G0, G |- s : G1    and   G1 |- V : L
       and  V[s] does not contain any skolem constants
       and  Rl is a list of reduction propositions
       and  G0, G |- Rl
       and  G0, G |- V[s]
     and
       V[s] satisfies the associated termination order
     *)
 checkClause(gQR,  , g,  , q,  , vs,  , occ) checkClauseW (gQR,  , g,  , q,  , whnf vs,  , occ) checkClauseW(gQR,  , g,  , q,  , (pi ((d,  , maybe),  , v),  , s),  , occ) checkClause (gQR,  , decl (g,  , decEName (g,  , decSub (d,  , s))),  , decl (q,  , exist),  , (v,  , dot1 s),  , body occ) checkClauseW(gQR,  , g,  , q,  , (pi ((d as dec (_,  , v1),  , no),  , v2),  , s),  , occ) checkClause (gQR,  , decl (g,  , decSub (d,  , s)),  , decl (q,  , and (label occ)),  , (v2,  , dot1 s),  , body occ) checkClauseW(gQR as (g0,  , q0,  , rl),  , g,  , q,  , vs as (root (const a,  , s),  , s),  , occ) let let  inlet  in in checkSubgoals (concat (g0,  , g),  , concat (q0,  , q),  , rl',  , vs,  , 0,  , (g,  , q)) checkClauseW(gQR,  , g,  , q,  , (root (def a,  , s),  , s),  , occ) raise (error' (occ,  , "Termination checking for defined type families not yet available:\n" ^ "Illegal use of " ^ qidToString (constQid a) ^ "."))let rec checkClause'(vs,  , occ) checkClause ((null,  , null,  , nil),  , null,  , null,  , vs,  , occ)(*-------------------------------------------------------------------*)
(* Reduction Checker *)
(* checkRGoal (G, Q, Rl, (V1, s1), occ) = Rl''

       Invariant
       If   G : Q
       and  G |- s1 : G1   and   G1 |- V1 : type
       and  V1[s1], V2[s2] does not contain Skolem constants
       and  G |- s2 : G2   and   G2 |- V2 : type
       and occ locates V1 in declaration
       and Rl is a context of reduction predicates
       and  G |- Rl
       and Rl implies that V1[s1] satisfies its associated reduction order

     *)
let rec checkRGoal(g,  , q,  , rl,  , vs,  , occ) checkRGoalW (g,  , q,  , rl,  , whnf vs,  , occ) checkRGoalW(g,  , q,  , rl,  , vs as (root (const a,  , s),  , s),  , occ) () checkRGoalW(g,  , q,  , rl,  , (pi ((d,  , maybe),  , v),  , s),  , occ) checkRGoal (decl (g,  , decLUName (g,  , decSub (d,  , s))),  , decl (q,  , all),  , shiftRCtx rl (fun s -> comp (s,  , shift)),  , (v,  , dot1 s),  , body occ) checkRGoalW(g,  , q,  , rl,  , (pi ((d as dec (_,  , v1),  , no),  , v2),  , s),  , occ) (checkRClause (g,  , q,  , rl,  , (v1,  , s),  , label occ); checkRGoal (g,  , q,  , rl,  , (v2,  , comp (invShift,  , s)),  , body occ)) checkRGoalW(g,  , q,  , rl,  , (root (def a,  , s),  , s),  , occ) raise (error' (occ,  , "Reduction checking for defined type families not yet available:\n" ^ "Illegal use of " ^ qidToString (constQid a) ^ "."))(* checkRImp (G, Q, Rl, (V1, s1), (V2, s2), occ) = ()

       Invariant
       If   G : Q
       and  G |- s1 : G1   and   G1 |- V1 : type
       and  V1[s1], V2[s2] does not contain Skolem constants
       and  G |- s2 : G2   and   G2 |- V2 : type
       and occ locates V1 in declaration
       and Rl is a context for derived reduction order assumptions
       and G |- Rl

       then Rl implies that  V2[s2] satisfies its associated reduction order
            with respect to V1[s1]
    *)
 checkRImp(g,  , q,  , rl,  , vs,  , vs',  , occ) checkRImpW (g,  , q,  , rl,  , whnf vs,  , vs',  , occ) checkRImpW(g,  , q,  , rl,  , (pi ((d',  , maybe),  , v'),  , s'),  , (v,  , s),  , occ) checkRImp (decl (g,  , decEName (g,  , decSub (d',  , s'))),  , decl (q,  , exist),  , shiftRCtx rl (fun s -> comp (s,  , shift)),  , (v',  , dot1 s'),  , (v,  , comp (s,  , shift)),  , occ) checkRImpW(g,  , q,  , rl,  , (pi ((d' as dec (_,  , v1),  , no),  , v2),  , s'),  , (v,  , s),  , occ) let let  in in checkRImp (g,  , q,  , rl',  , (v2,  , comp (invShift,  , s')),  , (v,  , s),  , occ) checkRImpW(g,  , q,  , rl,  , vs' as (root (const a,  , s),  , s),  , vs,  , occ) checkRGoal (g,  , q,  , rl,  , vs,  , occ) checkRImpW(g,  , q,  , rl,  , vs' as (root (def a,  , s),  , s),  , vs,  , occ) raise (error' (occ,  , "Reduction checking for defined type families not yet available:\n" ^ "Illegal use of " ^ qidToString (constQid a) ^ "."))(* checkRClause (G, Q, Rl, (V, s)) = ()

       Invariant:
       If G: Q
       and  G |- s : G1    and   G1 |- V : L
       and  V[s] does not contain any Skolem constants
       and  Rl is a context of reduction predicates
       and  G |- Rl
       then Rl implies that V[s] satifies the reduction order
    *)
 checkRClause(g,  , q,  , rl,  , vs,  , occ) checkRClauseW (g,  , q,  , rl,  , whnf vs,  , occ) checkRClauseW(g,  , q,  , rl,  , (pi ((d,  , maybe),  , v),  , s),  , occ) checkRClause (decl (g,  , decEName (g,  , decSub (d,  , s))),  , decl (q,  , exist),  , shiftRCtx rl (fun s -> comp (s,  , shift)),  , (v,  , dot1 s),  , body occ) checkRClauseW(g,  , q,  , rl,  , (pi ((d as dec (_,  , v1),  , no),  , v2),  , s),  , occ) let let  in(* N.decEName (G, I.decSub (D, s)) *)
let  in(* will not be used *)
let  inlet  in in checkRClause (g',  , q',  , rl'',  , (v2,  , dot1 s),  , body occ)checkRImp (g',  , q',  , rl'',  , (v2,  , dot1 s),  , (v1,  , comp (s,  , shift)),  , label occ) checkRClauseW(g,  , q,  , rl,  , vs as (root (const a,  , s),  , s),  , occ) let let  inlet  in in if deduce (g,  , q,  , rl,  , rO) then () else raise (error' (occ,  , "Reduction violation:\n" ^ rlistToString (g,  , rl) ^ " ---> " ^ (* rename ctx ??? *)
 orderToString (g,  , rO))) checkRClauseW(g,  , q,  , rl,  , vS as (root (def a,  , s),  , s),  , occ) raise (error' (occ,  , "Reduction checking for defined type families not yet available:\n" ^ "Illegal use of " ^ qidToString (constQid a) ^ "."))(* checkFamReduction a = ()

       Invariant:
       a is name of type family in the signature
       raises invariant, if clauses for a does not fulfill
       specified reducation property

       Note: checking reduction is a separate property of termination
    *)
let rec checkFamReductiona let let rec checkFam'[] (if ! chatter > 3 then print "\n" else (); ()) checkFam'(const (b) :: bs) (if (! chatter) > 3 then print (qidToString (constQid b) ^ " ") else (); (* reuse variable names when tracing *)
if (! chatter) > 4 then (varReset null; print "\n") else (); (try  with ); checkFam' bs) checkFam'(def (d) :: bs) (if (! chatter) > 3 then print (qidToString (constQid d) ^ " ") else (); (* reuse variable names when tracing *)
if (! chatter) > 4 then (varReset null; print "\n") else (); (try  with ); checkFam' bs)let  in in checkFam' (lookup a)(* checkFam a = ()

       Invariant:
       a is name of type family in the signature
       raises invariant, if clauses for a do not terminate
       according to specified termination order

       Note: termination checking takes into account proven
             reduction properties.
    *)
let rec checkFama let let rec checkFam'[] (if ! chatter > 3 then print "\n" else (); ()) checkFam'(const b :: bs) (if (! chatter) > 3 then print (qidToString (constQid b) ^ " ") else (); (* reuse variable names when tracing *)
if (! chatter) > 4 then (varReset null; print "\n") else (); (try  with ); checkFam' bs) checkFam'(def (d) :: bs) (if (! chatter) > 3 then print (qidToString (constQid d) ^ " ") else (); (* reuse variable names when tracing *)
if (! chatter) > 4 then (varReset null; print "\n") else (); (try  with ); checkFam' bs)let  in in checkFam' (lookup a)let rec reset() (reset (); resetROrder ())let  inlet  inlet  in(* local *)
end