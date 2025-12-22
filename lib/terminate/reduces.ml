(* Reduction and Termination checker *)


(* Author: Brigitte Pientka *)


(* for_sml termination checking see [Rohwedder,Pfenning ESOP'96]
   for_sml a revised version incorporating reducation checking see
   tech report CMU-CS-01-115
 *)


module Reduces (Global : GLOBAL) (Whnf : WHNF) (Names : NAMES) (Index : INDEX) (Subordinate : SUBORDINATE) (Formatter : FORMATTER) (Print : PRINT) (Order : ORDER) (Checking : CHECKING) (Origins : ORIGINS) : REDUCES = struct (*! structure IntSyn = IntSyn' !*)

exception Error of string
module I = IntSyn
module P = Paths
module N = Names
module F = Formatter
module R = Order
module C = Checking
exception Error' of P.occ * string
let rec error (c, occ, msg)  = (match Origins.originLookup c with (fileName, None) -> raise (Error (fileName ^ ":" ^ msg)) | (fileName, Some occDec) -> raise (Error (P.wrapLoc' (P.Loc (fileName, P.occToRegionDec occDec occ), Origins.linesInfoLookup (fileName), msg))))
let rec concat = function (G', I.Null) -> G' | (G', I.Decl (G, D)) -> I.Decl (concat (G', G), D)
(*--------------------------------------------------------------------*)

(* Printing *)

let rec fmtOrder (G, O)  = ( let rec fmtOrder' = function (R.Arg (Us, Vs)) -> F.Hbox [F.String "("; Print.formatExp (G, I.EClo Us); F.String ")"] | (R.Lex L) -> F.Hbox [F.String "{"; F.HOVbox0 1 0 1 (fmtOrders L); F.String "}"] | (R.Simul L) -> F.Hbox [F.String "["; F.HOVbox0 1 0 1 (fmtOrders L); F.String "]"]
and fmtOrders = function [] -> [] | (O :: []) -> fmtOrder' O :: [] | (O :: L) -> fmtOrder' O :: F.Break :: fmtOrders L in  fmtOrder' O )
let rec fmtComparison (G, O, comp, O')  = F.HOVbox0 1 0 1 [fmtOrder (G, O); F.Break; F.String comp; F.Break; fmtOrder (G, O')]
let rec fmtPredicate = function (G, C.Less (O, O')) -> fmtComparison (G, O, "<", O') | (G, C.Leq (O, O')) -> fmtComparison (G, O, "<=", O') | (G, C.Eq (O, O')) -> fmtComparison (G, O, "=", O') | (G, C.Pi (D, P)) -> F.Hbox [F.String "Pi "; fmtPredicate (I.Decl (G, D), P)]
let rec rlistToString' = function (G, []) -> "" | (G, [P]) -> F.makestring_fmt (fmtPredicate (G, P)) | (G, (P :: Rl)) -> F.makestring_fmt (fmtPredicate (G, P)) ^ " ," ^ rlistToString' (G, Rl)
let rec rlistToString (G, Rl)  = rlistToString' (Names.ctxName G, Rl)
let rec orderToString (G, P)  = F.makestring_fmt (fmtPredicate (Names.ctxName G, P))
(*--------------------------------------------------------------------*)

(* select (c, (S, s)) = P

      select parameters according to termination order

      Invariant:
      If   . |- c : V   G |- s : G'    G' |- S : V > type
      and  V = {x1:V1} ... {xn:Vn} type.
      then P = U1[s1] .. Un[sn] is parameter select of S[s] according to sel (c)
      and  G |- si : Gi  Gi |- Ui : Vi
      and  G |- Vi[s]  == V[si] : type   forall 1<=i<=n
    *)

let rec select (c, (S, s))  = ( let SO = R.selLookup c in let Vid = (I.constType c, I.id) in let rec select'' (n, (Ss', Vs''))  = select''W (n, (Ss', Whnf.whnf Vs''))
and select''W = function (1, ((I.App (U', S'), s'), (I.Pi ((I.Dec (_, V''), _), _), s''))) -> ((U', s'), (V'', s'')) | (n, ((I.SClo (S', s1'), s2'), Vs'')) -> select''W (n, ((S', I.comp (s1', s2')), Vs'')) | (n, ((I.App (U', S'), s'), (I.Pi ((I.Dec (_, V1''), _), V2''), s''))) -> select'' (n - 1, ((S', s'), (V2'', I.Dot (I.Exp (I.EClo (U', s')), s'')))) in let rec select' = function (R.Arg n) -> R.Arg (select'' (n, ((S, s), Vid))) | (R.Lex L) -> R.Lex (map select' L) | (R.Simul L) -> R.Simul (map select' L) in  select' (R.selLookup c) )
let rec selectOcc (c, (S, s), occ)  = try select (c, (S, s)) with R.Error (msg) -> raise (Error' (occ, "Termination violation: no order assigned for_sml " ^ N.qidToString (N.constQid c)))
(* selectROrder (c, (S, s)) = P

       select parameters according to reduction order

       Invariant:
       If   . |- c : V   G |- s : G'    G' |- S : V > type
       and  V = {x1:V1} ... {xn:Vn} type.
       then P = U1[s1] .. Un[sn] is parameter select of S[s] according to sel (c)
       and  G |- si : Gi  Gi |- Ui : Vi
       and  G |- Vi[s]  == V[si] : type   forall 1<=i<=n
    *)

let rec selectROrder (c, (S, s))  = ( let Vid = (I.constType c, I.id) in let rec select'' (n, (Ss', Vs''))  = select''W (n, (Ss', Whnf.whnf Vs''))
and select''W = function (1, ((I.App (U', S'), s'), (I.Pi ((I.Dec (_, V''), _), _), s''))) -> ((U', s'), (V'', s'')) | (n, ((I.SClo (S', s1'), s2'), Vs'')) -> select''W (n, ((S', I.comp (s1', s2')), Vs'')) | (n, ((I.App (U', S'), s'), (I.Pi ((I.Dec (_, V1''), _), V2''), s''))) -> select'' (n - 1, ((S', s'), (V2'', I.Dot (I.Exp (I.EClo (U', s')), s'')))) in let rec select' = function (R.Arg n) -> R.Arg (select'' (n, ((S, s), Vid))) | (R.Lex L) -> R.Lex (map select' L) | (R.Simul L) -> R.Simul (map select' L) in let rec selectP = function (R.Less (O1, O2)) -> C.Less (select' O1, select' O2) | (R.Leq (O1, O2)) -> C.Leq (select' O1, select' O2) | (R.Eq (O1, O2)) -> C.Eq (select' O1, select' O2) in  try Some (selectP (R.selLookupROrder c)) with R.Error (s) -> None )
(*--------------------------------------------------------------*)

(* abstractRO (G, D, RO) = Pi D. RO
       Invariant:

       If  G, D |- RO
       then  G |- Pi D . RO

    *)

let rec abstractRO (G, D, O)  = C.Pi (D, O)
(* getROrder (G, Q, (V, s)) = O
       If G: Q
       and  G |- s : G1    and   G1 |- V : L
       then O is the reduction order associated to V[s]
       and  G |- O

     *)

let rec getROrder (G, Q, Vs, occ)  = getROrderW (G, Q, Whnf.whnf Vs, occ)
and getROrderW = function (G, Q, Vs, occ) -> ( let O = selectROrder (a, (S, s)) in let _ = match O with None -> () | Some (O) -> if (! Global.chatter) > 5 then print ("Reduction predicate for_sml " ^ N.qidToString (N.constQid a) ^ " added : " ^ orderToString (G, O) ^ "\n") else () in  O ) | (G, Q, (I.Pi ((D, I.Maybe), V), s), occ) -> ( let O = getROrder (I.Decl (G, N.decLUName (G, I.decSub (D, s))), I.Decl (Q, C.All), (V, I.dot1 s), P.body occ) in  match O with None -> None | Some (O') -> Some (abstractRO (G, I.decSub (D, s), O')) ) | (G, Q, (I.Pi ((D, I.No), V2), s), occ) -> ( let O = getROrder (G, Q, (V2, I.comp (I.invShift, s)), P.body occ) in  match O with None -> None | Some (O') -> Some (O') ) | (G, Q, Vs, occ) -> raise (Error' (occ, "Reduction checking for_sml defined type families not yet available:\n" ^ "Illegal use of " ^ N.qidToString (N.constQid a) ^ "."))
(*--------------------------------------------------------------------*)

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

let rec checkGoal (G0, Q0, Rl, Vs, Vs', occ)  = checkGoalW (G0, Q0, Rl, Whnf.whnf Vs, Vs', occ)
and checkGoalW = function (G0, Q0, Rl, (I.Pi ((D, I.No), V2), s), Vs', occ) -> (checkClause ((G0, Q0, Rl), I.Null, I.Null, (V1, s), P.label occ); checkGoal (G0, Q0, Rl, (V2, I.comp (I.invShift, s)), Vs', P.body occ)) | (G0, Q0, Rl, (I.Pi ((D, I.Maybe), V), s), (V', s'), occ) -> checkGoal (I.Decl (G0, N.decLUName (G0, I.decSub (D, s))), I.Decl (Q0, C.All), C.shiftRCtx Rl (fun s -> I.comp (s, I.shift)), (V, I.dot1 s), (V', I.comp (s', I.shift)), P.body occ) | (G0, Q0, Rl, Vs, Vs', occ) -> ( (* only if a terminates? *)
(* always succeeds? -fp *)
(* always succeeds? -fp *)
let rec lookup = function (R.Empty, f) -> R.Empty | (a's, f) -> if (f a) then a's else lookup (a's', f) | (a's, f) -> if (f a) then a's else lookup (a's', f) in let P = selectOcc (a, (S, s), occ) in let P' = select (a', (S', s')) in let a's = Order.mutLookup a in  (match lookup (a's, fun x' -> x' = a') with R.Empty -> () | R.LE _ -> (if (! Global.chatter) > 4 then (print ("Verifying termination order:\n"); print (rlistToString (G0, Rl)); print (" ---> " ^ orderToString (G0, C.Leq (P, P')) ^ "\n")) else (); if C.deduce (G0, Q0, Rl, C.Leq (P, P')) then () else raise (Error' (occ, "Termination violation:\n" ^ rlistToString (G0, Rl) ^ " ---> " ^ orderToString (G0, C.Leq (P, P'))))) | R.LT _ -> (if (! Global.chatter) > 4 then (print "Verifying termination order:\n"; print (rlistToString (G0, Rl) ^ " ---> "); print (orderToString (G0, C.Less (P, P')) ^ "\n")) else (); if C.deduce (G0, Q0, Rl, C.Less (P, P')) then () else raise (Error' (occ, "Termination violation:\n" ^ rlistToString (G0, Rl) ^ " ---> " ^ orderToString (G0, C.Less (P, P')))))) ) | (G0, Q0, Rl, Vs, Vs', occ) -> raise (Error' (occ, "Reduction checking for_sml defined type families not yet available:\n" ^ "Illegal use of " ^ N.qidToString (N.constQid a) ^ ".")) | (G0, Q0, Rl, Vs, Vs', occ) -> raise (Error' (occ, "Reduction checking for_sml defined type families not yet available:\n" ^ "Illegal use of " ^ N.qidToString (N.constQid a') ^ "."))
and checkSubgoals = function (G0, Q0, Rl, Vs, n, (I.Decl (G, D), I.Decl (Q, C.And (occ)))) -> ( let _ = checkGoal (G0, Q0, Rl, (V', I.Shift (n + 1)), Vs, occ) in let RO = getROrder (G0, Q0, (V', I.Shift (n + 1)), occ) in let Rl' = match RO with None -> Rl | Some (O) -> O :: Rl in  checkSubgoals (G0, Q0, Rl', Vs, n + 1, (G, Q)) ) | (G0, Q0, Rl, Vs, n, (I.Decl (G, D), I.Decl (Q, C.Exist))) -> checkSubgoals (G0, Q0, Rl, Vs, n + 1, (G, Q)) | (G0, Q0, Rl, Vs, n, (I.Decl (G, D), I.Decl (Q, C.All))) -> checkSubgoals (G0, Q0, Rl, Vs, n + 1, (G, Q)) | (G0, Q0, Rl, Vs, n, (I.Null, I.Null)) -> ()
and checkClause (GQR, G, Q, Vs, occ)  = checkClauseW (GQR, G, Q, Whnf.whnf Vs, occ)
and checkClauseW = function (GQR, G, Q, (I.Pi ((D, I.Maybe), V), s), occ) -> checkClause (GQR, I.Decl (G, N.decEName (G, I.decSub (D, s))), I.Decl (Q, C.Exist), (V, I.dot1 s), P.body occ) | (GQR, G, Q, (I.Pi ((D, I.No), V2), s), occ) -> checkClause (GQR, I.Decl (G, I.decSub (D, s)), I.Decl (Q, C.And (P.label occ)), (V2, I.dot1 s), P.body occ) | (GQR, G, Q, Vs, occ) -> ( let n = I.ctxLength G in let Rl' = C.shiftRCtx Rl (fun s -> I.comp (s, I.Shift n)) in  checkSubgoals (concat (G0, G), concat (Q0, Q), Rl', Vs, 0, (G, Q)) ) | (GQR, G, Q, (I.Root (I.Def a, S), s), occ) -> raise (Error' (occ, "Termination checking for_sml defined type families not yet available:\n" ^ "Illegal use of " ^ N.qidToString (N.constQid a) ^ "."))
let rec checkClause' (Vs, occ)  = checkClause ((I.Null, I.Null, []), I.Null, I.Null, Vs, occ)
(*-------------------------------------------------------------------*)

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

let rec checkRGoal (G, Q, Rl, Vs, occ)  = checkRGoalW (G, Q, Rl, Whnf.whnf Vs, occ)
and checkRGoalW = function (G, Q, Rl, Vs, occ) -> () | (G, Q, Rl, (I.Pi ((D, I.Maybe), V), s), occ) -> checkRGoal (I.Decl (G, N.decLUName (G, I.decSub (D, s))), I.Decl (Q, C.All), C.shiftRCtx Rl (fun s -> I.comp (s, I.shift)), (V, I.dot1 s), P.body occ) | (G, Q, Rl, (I.Pi ((D, I.No), V2), s), occ) -> (checkRClause (G, Q, Rl, (V1, s), P.label occ); checkRGoal (G, Q, Rl, (V2, I.comp (I.invShift, s)), P.body occ)) | (G, Q, Rl, (I.Root (I.Def a, S), s), occ) -> raise (Error' (occ, "Reduction checking for_sml defined type families not yet available:\n" ^ "Illegal use of " ^ N.qidToString (N.constQid a) ^ "."))
and checkRImp (G, Q, Rl, Vs, Vs', occ)  = checkRImpW (G, Q, Rl, Whnf.whnf Vs, Vs', occ)
and checkRImpW = function (G, Q, Rl, (I.Pi ((D', I.Maybe), V'), s'), (V, s), occ) -> checkRImp (I.Decl (G, N.decEName (G, I.decSub (D', s'))), I.Decl (Q, C.Exist), C.shiftRCtx Rl (fun s -> I.comp (s, I.shift)), (V', I.dot1 s'), (V, I.comp (s, I.shift)), occ) | (G, Q, Rl, (I.Pi ((D', I.No), V2), s'), (V, s), occ) -> ( let Rl' = match getROrder (G, Q, (V1, s'), occ) with None -> Rl | Some (O) -> O :: Rl in  checkRImp (G, Q, Rl', (V2, I.comp (I.invShift, s')), (V, s), occ) ) | (G, Q, Rl, Vs', Vs, occ) -> checkRGoal (G, Q, Rl, Vs, occ) | (G, Q, Rl, Vs', Vs, occ) -> raise (Error' (occ, "Reduction checking for_sml defined type families not yet available:\n" ^ "Illegal use of " ^ N.qidToString (N.constQid a) ^ "."))
and checkRClause (G, Q, Rl, Vs, occ)  = checkRClauseW (G, Q, Rl, Whnf.whnf Vs, occ)
and checkRClauseW = function (G, Q, Rl, (I.Pi ((D, I.Maybe), V), s), occ) -> checkRClause (I.Decl (G, N.decEName (G, I.decSub (D, s))), I.Decl (Q, C.Exist), C.shiftRCtx Rl (fun s -> I.comp (s, I.shift)), (V, I.dot1 s), P.body occ) | (G, Q, Rl, (I.Pi ((D, I.No), V2), s), occ) -> ( (* N.decEName (G, I.decSub (D, s)) *)
(* will not be used *)
let G' = I.Decl (G, I.decSub (D, s)) in let Q' = I.Decl (Q, C.Exist) in let Rl' = C.shiftRCtx Rl (fun s -> I.comp (s, I.shift)) in let Rl'' = match getROrder (G', Q', (V1, I.comp (s, I.shift)), occ) with None -> Rl' | Some (O) -> O :: Rl' in  checkRClause (G', Q', Rl'', (V2, I.dot1 s), P.body occ); checkRImp (G', Q', Rl'', (V2, I.dot1 s), (V1, I.comp (s, I.shift)), P.label occ) ) | (G, Q, Rl, Vs, occ) -> ( let RO = match selectROrder (a, (S, s)) with None -> raise (Error' (occ, "No reduction order assigned for_sml " ^ N.qidToString (N.constQid a) ^ ".")) | Some (O) -> O in let _ = if ! Global.chatter > 4 then print ("Verifying reduction property:\n" ^ rlistToString (G, Rl) ^ " ---> " ^ orderToString (G, RO) ^ " \n") else () in  if C.deduce (G, Q, Rl, RO) then () else raise (Error' (occ, "Reduction violation:\n" ^ rlistToString (G, Rl) ^ " ---> " ^ (* rename ctx ??? *)
 orderToString (G, RO))) ) | (G, Q, Rl, VS, occ) -> raise (Error' (occ, "Reduction checking for_sml defined type families not yet available:\n" ^ "Illegal use of " ^ N.qidToString (N.constQid a) ^ "."))
(* checkFamReduction a = ()

       Invariant:
       a is name of type family in the signature
       raises invariant, if clauses for_sml a does not fulfill
       specified reducation property

       Note: checking reduction is a separate property of termination
    *)

let rec checkFamReduction a  = ( let rec checkFam' = function [] -> (if ! Global.chatter > 3 then print "\n" else (); ()) | (I.Const (b) :: bs) -> (if (! Global.chatter) > 3 then print (N.qidToString (N.constQid b) ^ " ") else (); (* reuse variable names when tracing *)
if (! Global.chatter) > 4 then (N.varReset IntSyn.Null; print "\n") else (); (try (checkRClause (I.Null, I.Null, [], (I.constType (b), I.id), P.top)) with Error' (occ, msg) -> error (b, occ, msg) | R.Error (msg) -> raise (Error (msg))); checkFam' bs) | (I.Def (d) :: bs) -> (if (! Global.chatter) > 3 then print (N.qidToString (N.constQid d) ^ " ") else (); (* reuse variable names when tracing *)
if (! Global.chatter) > 4 then (N.varReset IntSyn.Null; print "\n") else (); (try (checkRClause (I.Null, I.Null, [], (I.constType (d), I.id), P.top)) with Error' (occ, msg) -> error (d, occ, msg) | R.Error (msg) -> raise (Error (msg))); checkFam' bs) in let _ = if (! Global.chatter) > 3 then print ("Reduction checking family " ^ N.qidToString (N.constQid a) ^ ":\n") else () in  checkFam' (Index.lookup a) )
(* checkFam a = ()

       Invariant:
       a is name of type family in the signature
       raises invariant, if clauses for_sml a do not terminate
       according to specified termination order

       Note: termination checking takes into account proven
             reduction properties.
    *)

let rec checkFam a  = ( let rec checkFam' = function [] -> (if ! Global.chatter > 3 then print "\n" else (); ()) | (I.Const b :: bs) -> (if (! Global.chatter) > 3 then print (N.qidToString (N.constQid b) ^ " ") else (); (* reuse variable names when tracing *)
if (! Global.chatter) > 4 then (N.varReset IntSyn.Null; print "\n") else (); (try checkClause' ((I.constType (b), I.id), P.top) with Error' (occ, msg) -> error (b, occ, msg) | Order.Error (msg) -> raise (Error (msg))); checkFam' bs) | (I.Def (d) :: bs) -> (if (! Global.chatter) > 3 then print (N.qidToString (N.constQid d) ^ " ") else (); (* reuse variable names when tracing *)
if (! Global.chatter) > 4 then (N.varReset IntSyn.Null; print "\n") else (); (try checkClause' ((I.constType (d), I.id), P.top) with Error' (occ, msg) -> error (d, occ, msg) | Order.Error (msg) -> raise (Error (msg))); checkFam' bs) in let _ = if (! Global.chatter) > 3 then print ("Termination checking family " ^ N.qidToString (N.constQid a) ^ "\n") else () in  checkFam' (Index.lookup a) )
let rec reset ()  = (R.reset (); R.resetROrder ())
let reset = reset
let checkFamReduction = checkFamReduction
let checkFam = checkFam
(* local *)

 end


(* functor Reduces  *)

