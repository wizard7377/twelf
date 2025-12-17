OLDSearch  MetaGlobal METAGLOBAL    MetaSyn' METASYN    Whnf WHNF    Unify UNIFY    Index INDEX    Compile COMPILE    CPrint CPRINT    Print PRINT    Names NAMES     OLDSEARCH  struct (*! structure IntSyn = IntSyn' !*)
module (*! structure CompSyn = CompSyn' !*)
exception module module module let rec cidFromHead(const a) a cidFromHead(def a) a cidFromHead(skonst a) a(* only used for type families of compiled clauses *)
let rec eqHead(const a,  , const a') a = a' eqHead(def a,  , def a') a = a' eqHead_ false(* solve ((g,s), (G,dPool), sc, (acc, k)) => ()
     Invariants:
       G |- s : G'
       G' |- g :: goal
       G ~ dPool  (context G matches dPool)
       acc is the accumulator of results
       and k is the max search depth limit
           (used in the existential case for iterative deepening,
            used in the universal case for max search depth)
       if  G |- M :: g[s] then G |- sc :: g[s] => Answer, Answer closed
  *)
let rec solve((atom p,  , s),  , dp,  , sc,  , acck) matchAtom ((p,  , s),  , dp,  , sc,  , acck) solve((impl (r,  , a,  , h,  , g),  , s),  , dProg (g,  , dPool),  , sc,  , acck) let let  in in solve ((g,  , dot1 s),  , dProg (decl (g,  , d'),  , decl (dPool,  , dec (r,  , s,  , h))),  , (fun (m,  , acck') -> sc (lam (d',  , m),  , acck')),  , acck) solve((all (d,  , g),  , s),  , dProg (g,  , dPool),  , sc,  , acck) let let  in in solve ((g,  , dot1 s),  , dProg (decl (g,  , d'),  , decl (dPool,  , parameter)),  , (fun (m,  , acck') -> sc (lam (d',  , m),  , acck')),  , acck)(* rsolve ((p,s'), (r,s), (G,dPool), sc, (acc, k)) = ()
     Invariants:
       G |- s : G'
       G' |- r :: resgoal
       G |- s' : G''
       G'' |- p :: atom
       G ~ dPool
       acc is the accumulator of results
       and k is the max search depth limit
           (used in the existential case for iterative deepening,
            used in the universal case for max search depth)
       if G |- S :: r[s] then G |- sc : (r >> p[s']) => Answer
  *)
 rSolve(ps',  , (eq q,  , s),  , dProg (g,  , dPool),  , sc,  , acck as (acc,  , k)) if unifiable (g,  , ps',  , (q,  , s)) then sc (nil,  , acck) else acc rSolve(ps',  , (and (r,  , a,  , g),  , s),  , dp as dProg (g,  , dPool),  , sc,  , acck) let let  in in rSolve (ps',  , (r,  , dot (exp (x),  , s)),  , dp,  , (fun (s,  , acck') -> solve ((g,  , s),  , dp,  , (fun (m,  , acck'') -> (try  with )),  , acck')),  , acck) rSolve(ps',  , (exists (dec (_,  , a),  , r),  , s),  , dp as dProg (g,  , dPool),  , sc,  , acck) let let  in in rSolve (ps',  , (r,  , dot (exp (x),  , s)),  , dp,  , (fun (s,  , acck') -> sc (app (x,  , s),  , acck')),  , acck)(*    | rSolve (ps', (C.Axists (I.Dec (_, A), r), s), dp as C.DProg (G, dPool), sc, acck) =
        let
          val X = I.newEVar (G, I.EClo (A, s))
        in
          rSolve (ps', (r, I.Dot (I.Exp (X), s)), dp,
                  (fn (S, acck') => sc (S, acck')), acck)
        end
*)
(* aSolve ... *)
 aSolve((trivial,  , s),  , dp,  , sc,  , acc) sc ()(* Fri Jan 15 16:04:39 1999 -fp,cs
    | aSolve ((C.Unify(I.Eqn(e1, e2), ag), s), dp, sc, acc) =
      ((Unify.unify ((e1, s), (e2, s));
        aSolve ((ag, s), dp, sc, acc))
       handle Unify.Unify _ => acc)
     *)
(* matchatom ((p, s), (G, dPool), sc, (acc, k)) => ()
     G |- s : G'
     G' |- p :: atom
     G ~ dPool
     acc is the accumulator of results
     and k is the max search depth limit
         (used in the existential case for iterative deepening,
          used in the universal case for max search depth)
     if G |- M :: p[s] then G |- sc :: p[s] => Answer
  *)
 matchAtom(ps' as (root (ha,  , _),  , _),  , dp as dProg (g,  , dPool),  , sc,  , (acc,  , k)) let let rec matchSigacc' let let rec matchSig'(nil,  , acc'') acc'' matchSig'(hc :: sgn',  , acc'') let let  inlet  in in matchSig' (sgn',  , acc''') in matchSig' (lookup (cidFromHead ha),  , acc')let rec matchDProg(null,  , _,  , acc') matchSig acc' matchDProg(decl (dPool',  , dec (r,  , s,  , ha')),  , n,  , acc') if eqHead (ha,  , ha') then let let  in in matchDProg (dPool',  , n + 1,  , acc'') else matchDProg (dPool',  , n + 1,  , acc') matchDProg(decl (dPool',  , parameter),  , n,  , acc') matchDProg (dPool',  , n + 1,  , acc') in if k < 0 then acc else matchDProg (dPool,  , 1,  , acc)(* occursInExp (r, (U, s)) = B,

       Invariant:
       If    G |- s : G1   G1 |- U : V
       then  B holds iff r occurs in (the normal form of) U
    *)
let rec occursInExp(r,  , vs) occursInExpW (r,  , whnf vs) occursInExpW(r,  , (uni _,  , _)) false occursInExpW(r,  , (pi ((d,  , _),  , v),  , s)) occursInDec (r,  , (d,  , s)) || occursInExp (r,  , (v,  , dot1 s)) occursInExpW(r,  , (root (_,  , s),  , s)) occursInSpine (r,  , (s,  , s)) occursInExpW(r,  , (lam (d,  , v),  , s)) occursInDec (r,  , (d,  , s)) || occursInExp (r,  , (v,  , dot1 s)) occursInExpW(r,  , (eVar (r',  , _,  , v',  , _),  , s)) (r = r') || occursInExp (r,  , (v',  , s)) occursInExpW(r,  , (fgnExp csfe,  , s)) fold csfe (fun (u,  , b) -> b || occursInExp (r,  , (u,  , s))) false occursInSpine(_,  , (nil,  , _)) false occursInSpine(r,  , (sClo (s,  , s'),  , s)) occursInSpine (r,  , (s,  , comp (s',  , s))) occursInSpine(r,  , (app (u,  , s),  , s)) occursInExp (r,  , (u,  , s)) || occursInSpine (r,  , (s,  , s)) occursInDec(r,  , (dec (_,  , v),  , s)) occursInExp (r,  , (v,  , s))(* nonIndex (r, GE) = B

       Invariant:
       B hold iff
        r does not occur in any type of EVars in GE
    *)
let rec nonIndex(_,  , nil) true nonIndex(r,  , eVar (_,  , _,  , v,  , _) :: gE) (not (occursInExp (r,  , (v,  , id)))) && nonIndex (r,  , gE)(* select (GE, (V, s), acc) = acc'

       Invariant:
       If   GE is a list of Evars
       and  G |- s : G'   G' |- V : L
       then acc' is a list of EVars (G', X') s.t.
         (0) it extends acc'
         (1) (G', X') occurs in V[s]
         (2) (G', X') is not an index Variable to any (G, X) in acc'.
    *)
(* Efficiency: repeated whnf for every subterm in Vs!!! *)
let rec selectEVar(nil,  , _,  , acc) acc selectEVar((x as eVar (r,  , _,  , _,  , _)) :: gE,  , vs,  , acc) if occursInExp (r,  , vs) && nonIndex (r,  , acc) then selectEVar (gE,  , vs,  , x :: acc) else selectEVar (gE,  , vs,  , acc)(* searchEx' max (GE, sc) = acc'

       Invariant:
       If   GE is a list of EVars to be instantiated
       and  max is the maximal number of constructors
       then if an instantiation of EVars in GE is found Success is raised
            otherwise searchEx' terminates with []
    *)
(* contexts of EVars are recompiled for each search depth *)
let rec searchEx'max(nil,  , sc) [sc ()] searchEx'max(eVar (r,  , g,  , v,  , _) :: gE,  , sc) solve ((compileGoal (g,  , v),  , id),  , compileCtx false g,  , (fun (u',  , (acc',  , _)) -> (instantiateEVar (r,  , u',  , nil); searchEx' max (gE,  , sc))),  , (nil,  , max))(* deepen (f, P) = R'

       Invariant:
       If   f function expecting parameters P
         checking the variable MetaGlobal.maxLevel
       then R' is the result of applying f to P and
         traversing all possible numbers up to MetaGlobal.maxLevel
    *)
let rec deepenfp let let rec deepen'(level,  , acc) if level > (! maxFill) then acc else (if ! chatter > 5 then print "#" else (); deepen' (level + 1,  , f level p)) in deepen' (1,  , nil)(* searchEx (G, GE, (V, s), sc) = acc'
       Invariant:
       If   G |- s : G'   G' |- V : level
       and  GE is a list of EVars contained in V[s]
         where G |- X : VX
       and  sc is a function to be executed after all non-index variables have
         been instantiated
       then acc' is a list containing the one result from executing the success continuation
         All EVar's got instantiated with the smallest possible terms.
    *)
let rec searchEx(g,  , gE,  , vs,  , sc) (if ! chatter > 5 then print "[Search: " else (); deepen searchEx' (selectEVar (gE,  , vs,  , nil),  , fun params -> (if ! chatter > 5 then print "OK]\n" else (); sc params)); if ! chatter > 5 then print "FAIL]\n" else (); raise (error "No object found"))(* searchAll' (GE, acc, sc) = acc'

       Invariant:
       If   GE is a list of EVars to be instantiated
       and  acc is list of already collected results of the success continuation
       then acc' is an extension of acc', containing the results of sc
         after trying all combinations of instantiations of EVars in GE
    *)
(* Shared contexts of EVars in GE may recompiled many times *)
let rec searchAll'(nil,  , acc,  , sc) sc (acc) searchAll'(eVar (r,  , g,  , v,  , _) :: gE,  , acc,  , sc) solve ((compileGoal (g,  , v),  , id),  , compileCtx false g,  , (fun (u',  , (acc',  , _)) -> (instantiateEVar (r,  , u',  , nil); searchAll' (gE,  , acc',  , sc))),  , (acc,  , ! maxFill))(* searchAll (G, GE, (V, s), sc) = acc'

       Invariant:
       If   G |- s : G'   G' |- V : level
       and  GE is a list of EVars contained in V[s]
         where G |- X : VX
       and  sc is a function to be executed after all non-index variables have
         been instantiated
       then acc' is a list of results from executing the success continuation
    *)
let rec searchAll(g,  , gE,  , vs,  , sc) searchAll' (selectEVar (gE,  , vs,  , nil),  , nil,  , sc)let  inlet  in(* local ... *)
end