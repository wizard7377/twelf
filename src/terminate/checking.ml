Checking  Global GLOBAL    Whnf WHNF    Conv CONV    Unify UNIFY    Names NAMES    Index INDEX    Subordinate SUBORDINATE    Formatter FORMATTER    Print PRINT    Print Formatter  Formatter   Order ORDER    Origins ORIGINS     CHECKING  struct (*! structure IntSyn = IntSyn' !*)
module (*! structure Paths = Paths !*)
type Quantifier(*     | And                     *)
(* If Q marks all parameters in a context G we write   G : Q               *)
type Predicate(* Abbreviation *)
type Order(* reduction order assumptions (unordered) *)
type Rctx(* mixed prefix order contex *)
type Qctxmodule module module module module (* Reasoning about order relations *)
(*
    Typing context        G
    mixed prefix context  Q  := . | All | Existental

    Orders                0  := U[s1] : V[s2] | Lex O1 ... On | Simul O1 ... On
    Order Relation        P  := O < O' | O <= O' | O = O'

    Atomic Order Relation P' := U[s1] : V[s2] <  U'[s1'] : V'[s2'] |
                                U[s1] : V[s2] <= U'[s1'] : V'[s2'] |
                                U[s1] : V[s2] =  U'[s1'] : V'[s2']

    Order Relation Ctx    D  := . | R , D
    Atomic Order Rel. Ctx D' := . | R',  D'

    Invariant:

    sometimes we write G |- P as an abbreviation

    if P = (O < O')    then G |- O and G |- O'
    if P = (O <= O')    then G |- O and G |- O'
    if P = (O = O')    then G |- O and G |- O'

    if O = Lex O1 .. On  then G |- O1 and ....G |- On
    if O = Simul O1 .. On  then G |- O1 and ....G |- On

    if O = U[s1] : V[s2]
      then     G : Q
           and G |- s1 : G1, G1 |- U : V1
           and G |- s2 : G2   G2 |- V : L
           and G |- U[s1] : V[s2]

  *)
(*--------------------------------------------------------------------*)
(* Printing atomic orders *)
let rec atomicPredToString(g,  , less ((us,  , _),  , (us',  , _))) expToString (g,  , eClo (us)) ^ " < " ^ expToString (g,  , eClo (us')) atomicPredToString(g,  , leq ((us,  , _),  , (us',  , _))) expToString (g,  , eClo (us)) ^ " <= " ^ expToString (g,  , eClo (us')) atomicPredToString(g,  , eq ((us,  , _),  , (us',  , _))) expToString (g,  , eClo (us)) ^ " = " ^ expToString (g,  , eClo (us'))let rec atomicRCtxToString(g,  , nil) " " atomicRCtxToString(g,  , o :: nil) atomicPredToString (g,  , o) atomicRCtxToString(g,  , o :: d') atomicRCtxToString (g,  , d') ^ ", " ^ atomicPredToString (g,  , o)(*--------------------------------------------------------------------*)
(* shifting substitutions *)
(* shiftO O f = O'

      if O is an order
         then we shift the substitutions which are associated
         with its terms by applying f to it
    *)
let rec shiftO(arg ((u,  , us),  , (v,  , vs)))f arg ((u,  , (f us)),  , (v,  , (f vs))) shiftO(lex l)f lex (map (fun o -> shiftO o f) l) shiftO(simul l)f simul (map (fun o -> shiftO o f) l)let rec shiftP(less (o1,  , o2))f less (shiftO o1 f,  , shiftO o2 f) shiftP(leq (o1,  , o2))f leq (shiftO o1 f,  , shiftO o2 f) shiftP(eq (o1,  , o2))f eq (shiftO o1 f,  , shiftO o2 f) shiftP(pi (d as dec (x,  , v),  , p))f pi (d,  , shiftP p f)let rec shiftRCtxrlf map (fun p -> shiftP p f) rllet rec shiftArg(less (((u1,  , s1),  , (v1,  , s1')),  , ((u2,  , s2),  , (v2,  , s2'))))f less (((u1,  , (f s1)),  , (v1,  , (f s1'))),  , (((u2,  , (f s2)),  , (v2,  , (f s2'))))) shiftArg(leq (((u1,  , s1),  , (v1,  , s1')),  , ((u2,  , s2),  , (v2,  , s2'))))f leq (((u1,  , (f s1)),  , (v1,  , (f s1'))),  , (((u2,  , (f s2)),  , (v2,  , (f s2'))))) shiftArg(eq (((u1,  , s1),  , (v1,  , s1')),  , ((u2,  , s2),  , (v2,  , s2'))))f eq (((u1,  , (f s1)),  , (v1,  , (f s1'))),  , (((u2,  , (f s2)),  , (v2,  , (f s2')))))let rec shiftACtxrlf map (fun p -> shiftArg p f) rl(*--------------------------------------------------------------------*)
(* Printing *)
let rec fmtOrder(g,  , o) let let rec fmtOrder'(arg (us as (u,  , s),  , vs as (v,  , s'))) hbox [string "("; formatExp (g,  , eClo us); string ")"] fmtOrder'(lex l) hbox [string "{"; hOVbox0 1 0 1 (fmtOrders l); string "}"] fmtOrder'(simul l) hbox [string "["; hOVbox0 1 0 1 (fmtOrders l); string "]"] fmtOrders[] [] fmtOrders(o :: []) fmtOrder' o :: [] fmtOrders(o :: l) fmtOrder' o :: break :: fmtOrders l in fmtOrder' olet rec fmtComparison(g,  , o,  , comp,  , o') hOVbox0 1 0 1 [fmtOrder (g,  , o); break; string comp; break; fmtOrder (g,  , o')]let rec fmtPredicate'(g,  , less (o,  , o')) fmtComparison (g,  , o,  , "<",  , o') fmtPredicate'(g,  , leq (o,  , o')) fmtComparison (g,  , o,  , "<=",  , o') fmtPredicate'(g,  , eq (o,  , o')) fmtComparison (g,  , o,  , "=",  , o') fmtPredicate'(g,  , pi (d,  , p)) hbox [string "Pi "; fmtPredicate' (decl (g,  , d),  , p)]let rec fmtPredicate(g,  , p) fmtPredicate' (ctxName g,  , p)let rec fmtRGCtx'(g,  , nil) "" fmtRGCtx'(g,  , [p]) makestring_fmt (fmtPredicate' (g,  , p)) fmtRGCtx'(g,  , (p :: rl)) makestring_fmt (fmtPredicate' (g,  , p)) ^ " ," ^ fmtRGCtx' (g,  , rl)let rec fmtRGCtx(g,  , rl) fmtRGCtx' (ctxName g,  , rl)(*--------------------------------------------------------------------*)
(* init () = true

       Invariant:
       The inital constraint continuation
    *)
let rec init() truelet rec eqCid(c,  , c') (c = c')let rec conv((us,  , vs),  , (us',  , vs')) conv (vs,  , vs') && conv (us,  , us')let rec isUniversal(all) true isUniversal(exist) false isUniversal(exist') falselet rec isExistential(all) false isExistential(exist) true isExistential(exist') true(* isParameter (Q, X) = B

       Invariant:
       If   G |- X : V
       and  G : Q
       then B holds iff X is unrestricted (uninstantiated and free
       of constraints, or lowered only) or instantiated to a universal parameter
    *)
let rec isParameter(q,  , x) isParameterW (q,  , whnf (x,  , id)) isParameterW(q,  , us) try  with (* isFreeEVar (Us) = true
       iff Us represents a possibly lowered uninstantiated EVar.

       Invariant: it participated only in matching, not full unification
    *)
 isFreeEVar(eVar (_,  , _,  , _,  , ref []),  , _) true isFreeEVar(lam (d,  , u),  , s) isFreeEVar (whnf (u,  , dot1 s)) isFreeEVar_ false(* isAtomic (G, X) = true
       Invariant:
       If G |- X : V
       and G : Q
       then B holds iff X is an atomic term which is not a parameter
     *)
let rec isAtomic(gQ,  , us) isAtomicW (gQ,  , whnf us) isAtomicW(gQ,  , (x as root (const c,  , s),  , s)) isAtomicS (gQ,  , (s,  , s)) isAtomicW(gQ,  , (x as root (def c,  , s),  , s)) isAtomicS (gQ,  , (s,  , s)) isAtomicW(gQ as (g,  , q),  , (x as root (bVar n,  , s),  , s)) isExistential (ctxLookup (q,  , n)) || isAtomicS (gQ,  , (s,  , s)) isAtomicW(gQ,  , _) false isAtomicS(gQ,  , (nil,  , _)) true isAtomicS(gQ,  , (sClo (s,  , s'),  , s'')) isAtomicS (gQ,  , (s,  , comp (s',  , s''))) isAtomicS(gQ,  , (app (u',  , s'),  , s1')) false(*-----------------------------------------------------------*)
(* eq (G, ((U, s1), (V, s2)), ((U', s1'), (V', s2')), sc) = B

       Invariant:
       B holds  iff
            G |- s1 : G1   G1 |- U : V1
       and  G |- s2 : G2   G2 |- V : L
       and  G |- U[s1] : V[s2]
       and  G |- s' : G3  G3 |- U' : V'
       and  U[s1] is unifiable with to U'[s']
       and  all restrictions in sc are satisfied
       and V[s2] is atomic
       and only U'[s'] contains EVars
    *)
let rec eq(g,  , (us,  , vs),  , (us',  , vs')) unifiable (g,  , vs,  , vs') && unifiable (g,  , us,  , us')(* lookupEq (GQ, D, UsVs, UsVs', sc) = B

     B holds iff

     and  D is an atomic order relation ctx
     and  UsVs and UsVs' are atomic and may contain EVars

          G : Q
     and  G |- s1 : G1   G1 |- U : V1
     and  G |- s2 : G2   G2 |- V : L
     and  G |- U[s1] : V [s2]
     and  G |- s' : G3  G3 |- U' : V'

     if there exists Eq(UsVs1, UsVs1') in D
        s.t. UsVs1 unifies with UsVs and
             UsVs1' unifies with UsVs' and
             all restrictions in sc are satisfied
     or
     if there exists Eq(UsVs1, UsVs1') in D
        s.t. UsVs1' unifies with UsVs and
             UsVs1 unifies with UsVs' and
             all restrictions in sc are satisfied
             (symmetry)


    *)
let rec lookupEq(gQ,  , nil,  , usVs,  , usVs',  , sc) false lookupEq(gQ,  , (less (_,  , _) :: d),  , usVs,  , usVs',  , sc) lookupEq (gQ,  , d,  , usVs,  , usVs',  , sc) lookupEq(gQ as (g,  , q),  , (eq (usVs1,  , usVs1') :: d),  , usVs,  , usVs',  , sc) trail (fun () -> eq (g,  , usVs1,  , usVs) && eq (g,  , usVs1',  , usVs') && sc ()) || trail (fun () -> eq (g,  , usVs1,  , usVs') && eq (g,  , usVs1',  , usVs) && sc ()) || lookupEq (gQ,  , d,  , usVs,  , usVs',  , sc)(* lookupLt (GQ, D, UsVs, UsVs', sc) = B

     B holds iff

     and  D is an atomic order relation ctx
     and  UsVs and UsVs' are atomic and may contain EVars

          G : Q
     and  G |- s1 : G1   G1 |- U : V1
     and  G |- s2 : G2   G2 |- V : L
     and  G |- U[s1] : V [s2]
     and  G |- s' : G3  G3 |- U' : V'

     if there exists Less(UsVs1, UsVs1') in D
        s.t. UsVs1 unifies with UsVs and
             UsVs1' unifies with UsVs' and
             all restrictions in sc are satisfied
    *)
let rec lookupLt(gQ,  , nil,  , usVs,  , usVs',  , sc) false lookupLt(gQ,  , (eq (_,  , _) :: d),  , usVs,  , usVs',  , sc) lookupLt (gQ,  , d,  , usVs,  , usVs',  , sc) lookupLt(gQ as (g,  , q),  , (less (usVs1,  , usVs1') :: d),  , usVs,  , usVs',  , sc) trail (fun () -> eq (g,  , usVs1,  , usVs) && eq (g,  , usVs1',  , usVs') && sc ()) || lookupLt (gQ,  , d,  , usVs,  , usVs',  , sc)(*  eqAtomic (GQ, D, D', UsVs, UsVs', sc) = B

        B iff
            UsVs unifies with UsVs'                (identity)
        or  D, UsVs = UsVs', D' ---> UsVs = UsVs'  (ctx lookup)
        or  D, UsVs' = UsVs, D' ---> UsVs = UsVs'  (ctx lookup + symmetry)
        or  D, D' ---> UsVs = UsVs' by transitivity

     *)
let rec eqAtomic(gQ as (g,  , q),  , nil,  , d',  , usVs,  , usVs',  , sc) trail (fun () -> eq (g,  , usVs,  , usVs') && sc ()) || lookupEq (gQ,  , d',  , usVs,  , usVs',  , sc) eqAtomic(gQ as (g,  , q),  , d,  , d',  , usVs,  , usVs',  , sc) trail (fun () -> eq (g,  , usVs,  , usVs') && sc ()) || lookupEq (gQ,  , d,  , usVs,  , usVs',  , sc) || lookupEq (gQ,  , d',  , usVs,  , usVs',  , sc) || transEq (gQ,  , d,  , d',  , usVs,  , usVs',  , sc)(* transEq (GQ, D, D', UsVs, UsVs', sc) = B

     B iff
        if D, UsVs' = UsVs1 ; D' ---> UsVs = UsVs'
          then  D, D' ---> UsVs = UsVs1            (transEq1)

        or

        if D, UsVs1 = UsVs'; D' ---> UsVs = UsVs'  (transEq2)
          then  D, D' ---> UsVs = UsVs1

       or

       if D, UsVs1 = UsVs'; D' ---> UsVs = UsVs'
         then D; UsVs1 = UsVs' D' ---> UsVs = UsVs'
   *)
 transEq(gQ as (g,  , q),  , nil,  , d,  , usVs,  , usVs',  , sc) false transEq(gQ as (g,  , q),  , (eq (usVs1,  , usVs1') :: d),  , d',  , usVs,  , usVs',  , sc) trail (fun () -> eq (g,  , usVs1',  , usVs') && sc () && eqAtomicR (gQ,  , (d @ d'),  , usVs,  , usVs1,  , sc,  , atomic)) || trail (fun () -> eq (g,  , usVs1,  , usVs') && sc () && eqAtomicR (gQ,  , (d @ d'),  , usVs,  , usVs1',  , sc,  , atomic)) || transEq (gQ,  , d,  , (eq (usVs1,  , usVs1') :: d'),  , usVs,  , usVs',  , sc) transEq(gQ as (g,  , q),  , (less (usVs1,  , usVs1') :: d),  , d',  , usVs,  , usVs',  , sc) transEq (gQ,  , d,  , d',  , usVs,  , usVs',  , sc)(* ltAtomic (GQ, D, D', UsVs, UsVs', sc) = B

     B iff
        if D, UsVs <UsVs' ; D' ---> UsVs < UsVs'   (identity)

        or

        if D, UsVs1 = UsVs'; D' ---> UsVs = UsVs'  (transEq2)
          then  D, D' ---> UsVs = UsVs1

       or

       if D, UsVs1 = UsVs'; D' ---> UsVs = UsVs'
         then D; UsVs1 = UsVs' D' ---> UsVs = UsVs'
   *)
 ltAtomic(gQ as (g,  , q),  , nil,  , d',  , usVs,  , usVs',  , sc) lookupLt (gQ,  , d',  , usVs,  , usVs',  , sc) ltAtomic(gQ as (g,  , q),  , d,  , d',  , usVs,  , usVs',  , sc) lookupLt (gQ,  , d,  , usVs,  , usVs',  , sc) || lookupLt (gQ,  , d',  , usVs,  , usVs',  , sc) || transLt (gQ,  , d,  , d',  , usVs,  , usVs',  , sc)(* transLt (GQ, D, D', UsVs, UsVs', sc) = B

     B iff
        if D, UsVs' = UsVs1 ; D' ---> UsVs = UsVs'
          then  D, D' ---> UsVs = UsVs1            (transEq1)

        or

        if D, UsVs1 = UsVs'; D' ---> UsVs = UsVs'  (transEq2)
          then  D, D' ---> UsVs = UsVs1

       or

       if D, UsVs1 = UsVs'; D' ---> UsVs = UsVs'
         then D; UsVs1 = UsVs' D' ---> UsVs = UsVs'
   *)
 transLt(gQ as (g,  , q),  , nil,  , d,  , usVs,  , usVs',  , sc) false transLt(gQ as (g,  , q),  , (eq (usVs1,  , usVs1') :: d),  , d',  , usVs,  , usVs',  , sc) trail (fun () -> eq (g,  , usVs1',  , usVs') && sc () && ltAtomicR (gQ,  , (d @ d'),  , usVs,  , usVs1,  , sc,  , atomic)) || trail (fun () -> eq (g,  , usVs1,  , usVs') && sc () && ltAtomicR (gQ,  , (d @ d'),  , usVs,  , usVs1',  , sc,  , atomic)) || transLt (gQ,  , d,  , (eq (usVs1,  , usVs1') :: d'),  , usVs,  , usVs',  , sc) transLt(gQ as (g,  , q),  , (less (usVs1,  , usVs1') :: d),  , d',  , usVs,  , usVs',  , sc) trail (fun () -> eq (g,  , usVs1',  , usVs') && sc () && eqAtomicR (gQ,  , (d @ d'),  , usVs,  , usVs1,  , sc,  , atomic)) || trail (fun () -> eq (g,  , usVs1',  , usVs') && sc () && ltAtomicR (gQ,  , (d @ d'),  , usVs,  , usVs1,  , sc,  , atomic)) || transLt (gQ,  , d,  , (less (usVs1,  , usVs1') :: d'),  , usVs,  , usVs',  , sc)(* atomic (GQ, D, P) = B

     An atomic order context D' is maximally decomposed iff

          T := Root(c, Nil) | Root(n, Nil)
    and   T' := Root(c,S) | Root(n, S)
    and   all atomic order relations in D' are
          either T' < T or T1' = T1'

   An atomic order P' is maximally decomposed iff
          T := Root(c, nil) | Root(n, Nil)
    and   T' := Root(c,S) | Root(n, S)
    and   T' < T or T1 = T1

    Invariant:

    B iff
          D and P are maximally decomposed,
      and they may contain EVars
      and G : Q
      and G |- P
      and G |- D
      and D --> P

      *)
 atomic(gQ,  , d,  , d',  , eq (usVs,  , usVs'),  , sc) eqAtomic (gQ,  , d,  , d',  , usVs,  , usVs',  , sc) atomic(gQ,  , d,  , d',  , less (usVs,  , usVs'),  , sc) ltAtomic (gQ,  , d,  , d',  , usVs,  , usVs',  , sc)(*-----------------------------------------------------------*)
(* leftInstantiate ((G,Q), D, D', P, sc) = B

     B iff
           G : Q
       and G |- D
       and G |- D'
       and G |- P

       and  D is an atomic order relation ctx, which does not
              contain any EVars
       and  D' is an atomic order relation ctx, which may
              contain EVars
       and  P' is a atomic order relation

       and  D --> P

    D' accumulates all orders
    *)
 leftInstantiate(gQ as (g,  , q),  , nil,  , d',  , p,  , sc) if atomic (gQ,  , d',  , nil,  , p,  , sc) then (if ! chatter > 4 then print (" Proved: " ^ atomicRCtxToString (g,  , d') ^ " ---> " ^ atomicPredToString (g,  , p) ^ "\n") else (); true) else (* should never happen by invariant *)
false leftInstantiate(gQ,  , (less (usVs,  , usVs') :: d),  , d',  , p,  , sc) ltInstL (gQ,  , d,  , d',  , usVs,  , usVs',  , p,  , sc) leftInstantiate(gQ,  , (leq (usVs,  , usVs') :: d),  , d',  , p,  , sc) leInstL (gQ,  , d,  , d',  , usVs,  , usVs',  , p,  , sc) leftInstantiate(gQ,  , (eq (usVs,  , usVs') :: d),  , d',  , p,  , sc) eqInstL (gQ,  , d,  , d',  , usVs,  , usVs',  , p,  , sc)(* ltInstL ((G, Q), D, D', UsVs, UsVs', P, sc) = B
     Invariant:
       B holds  iff
            G : Q
       and  D is an atomic order relation ctx
       and  D' is an atomic order relation ctx
       and  P' is a atomic order relation

       and  G |- s1 : G1   G1 |- U : V1
       and  G |- s2 : G2   G2 |- V : L
       and  G |- U[s1] : V [s2]
       and  G |- s' : G3  G3 |- U' : V'
       and  sc is a constraint continuation representing restrictions on EVars
       and  V[s2] atomic
       and  only U[s1] contains EVars
       and  D, D', U[s1] < U'[s'] ---> P
    *)
 ltInstL(gQ,  , d,  , d',  , usVs,  , usVs',  , p',  , sc) ltInstLW (gQ,  , d,  , d',  , whnfEta usVs,  , usVs',  , p',  , sc) ltInstLW(gQ as (g,  , q),  , d,  , d',  , ((lam (dec as dec (_,  , v1),  , u),  , s1),  , (pi ((dec (_,  , v2),  , _),  , v),  , s2)),  , ((u',  , s1'),  , (v',  , s2')),  , p',  , sc) if equiv (targetFam v',  , targetFam v1)(* == I.targetFam V2' *)
 then let let  in(* = I.newEVar (I.EClo (V2', s2')) *)
(* enforces that X can only bound to parameter or remain uninstantiated *)
let  in in ltInstL ((g,  , q),  , d,  , d',  , ((u,  , dot (exp (x),  , s1)),  , (v,  , dot (exp (x),  , s2))),  , ((u',  , s1'),  , (v',  , s2')),  , p',  , sc') else if below (targetFam v1,  , targetFam v') then let let  in(* = I.newEVar (I.EClo (V2', s2')) *)
 in ltInstL ((g,  , q),  , d,  , d',  , ((u,  , dot (exp (x),  , s1)),  , (v,  , dot (exp (x),  , s2))),  , ((u',  , s1'),  , (v',  , s2')),  , p',  , sc) else false ltInstLW(gQ,  , d,  , d',  , usVs,  , usVs',  , p',  , sc) leftInstantiate (gQ,  , d,  , (less (usVs,  , usVs') :: d'),  , p',  , sc)(* leInstL ((G, Q), D, D', UsVs, UsVs', P', sc) = B
     Invariant:
       B holds  iff
            G : Q
       and  D is an atomic order relation ctx
       and  D' is an atomic order relation ctx
       and  P' is a atomic order relation

       and  G |- s1 : G1   G1 |- U : V1
       and  G |- s2 : G2   G2 |- V : L
       and  G |- U[s1] : V [s2]
       and  G |- s' : G3  G3 |- U' : V'
       and  sc is a constraint continuation representing restrictions on EVars
       and  V[s2] atomic
       and  only U[s1] contains EVars
       and  D, D', U[s1] <= U'[s'] ---> P'
    *)
 leInstL(gQ,  , d,  , d',  , usVs,  , usVs',  , p',  , sc) leInstLW (gQ,  , d,  , d',  , whnfEta usVs,  , usVs',  , p',  , sc) leInstLW(gQ as (g,  , q),  , d,  , d',  , ((lam (dec (_,  , v1),  , u),  , s1),  , (pi ((dec (_,  , v2),  , _),  , v),  , s2)),  , ((u',  , s1'),  , (v',  , s2')),  , p',  , sc) if equiv (targetFam v',  , targetFam v1)(* == I.targetFam V2' *)
 then let let  in(* = I.newEVar (I.EClo (V2', s2')) *)
(* enforces that X can only bound to parameter or remain uninstantiated *)
let  in in leInstL ((g,  , q),  , d,  , d',  , ((u,  , dot (exp (x),  , s1)),  , (v,  , dot (exp (x),  , s2))),  , ((u',  , s1'),  , (v',  , s2')),  , p',  , sc') else if below (targetFam v1,  , targetFam v') then let let  in(* = I.newEVar (I.EClo (V2', s2')) *)
 in leInstL ((g,  , q),  , d,  , d',  , ((u,  , dot (exp (x),  , s1)),  , (v,  , dot (exp (x),  , s2))),  , ((u',  , s1'),  , (v',  , s2')),  , p',  , sc) else false leInstLW(gQ,  , d,  , d',  , usVs,  , usVs',  , p,  , sc) leftInstantiate (gQ,  , d,  , (less (usVs,  , usVs') :: d'),  , p,  , sc)(* eqInstL ((G, Q), D, D', UsVs, UsVs', P, sc) = B

     Invariant:
       B holds  iff
            G : Q
       and  D is an atomic order relation ctx
       and  D' is an atomic order relation ctx
       and  P' is a atomic order relation
       and  G |- s1 : G1   G1 |- U : V1
       and  G |- s2 : G2   G2 |- V : L
       and  G |- U[s1] : V [s2]
       and  G |- s' : G3  G3 |- U' : V'
       and  sc is a constraint continuation representing restrictions on EVars
       and  V[s2] atomic
       and  only U[s1] and U'[s'] contain EVars
       and  D, D', U[s1] = U'[s'] ---> P'
    *)
 eqInstL(gQ,  , d,  , d',  , usVs,  , usVs',  , p',  , sc) eqInstLW (gQ,  , d,  , d',  , whnfEta usVs,  , whnfEta usVs',  , p',  , sc) eqInstLW(gQ as (g,  , q),  , d,  , d',  , ((lam (dec (_,  , v1'),  , u'),  , s1'),  , (pi ((dec (_,  , v2'),  , _),  , v'),  , s2')),  , ((lam (dec (_,  , v1''),  , u''),  , s1''),  , (pi ((dec (_,  , v2''),  , _),  , v''),  , s2'')),  , p',  , sc) let let  in(* = I.newEVar (I.EClo (V2', s2')) *)
 in eqInstL (gQ,  , d,  , d',  , ((u',  , dot (exp (x),  , s1')),  , (v',  , dot (exp (x),  , s2'))),  , ((u'',  , dot (exp (x),  , s1'')),  , (v'',  , dot (exp (x),  , s2''))),  , p',  , fun () -> (isParameter (q,  , x); sc ())) eqInstLW(gQ,  , d,  , d',  , usVs,  , usVs',  , p',  , sc) eqIL (gQ,  , d,  , d',  , usVs,  , usVs',  , p',  , sc)(* eqIL ((G, Q), D, D', UsVs, UsVs', P, sc) = B

     Invariant:
       B holds  iff
            G : Q
       and  D is an atomic order relation ctx
       and  D' is an atomic order relation ctx
       and  P' is a atomic order relation
       and  G |- s1 : G1   G1 |- U : V1
       and  G |- s2 : G2   G2 |- V : L
       and  G |- U[s1] : V [s2]
       and  G |- s' : G3  G3 |- U' : V'
       and  sc is a constraint continuation representing restrictions on EVars
       and  V[s2] atomic
       and  only U[s1] and U'[s'] contain EVars
       and  D, D', U[s1] = U'[s'] ---> P'
       and U, U' will be maximally unfolded
    *)
 eqIL(gQ as (g,  , q),  , d,  , d',  , usVs as ((root (const c,  , s),  , s),  , vs),  , usVs' as ((root (const c',  , s'),  , s'),  , vs'),  , p',  , sc) if eqCid (c,  , c') then eqSpineIL (gQ,  , d,  , d',  , ((s,  , s),  , (constType c,  , id)),  , ((s',  , s'),  , (constType c',  , id)),  , p',  , sc) else (if ! chatter > 4 then print (" Proved: " ^ atomicRCtxToString (g,  , (eq (usVs,  , usVs') :: d)) ^ atomicRCtxToString (g,  , d') ^ " ---> " ^ atomicPredToString (g,  , p') ^ "\n") else (); true) eqIL(gQ as (g,  , q),  , d,  , d',  , usVs as ((root (def c,  , s),  , s),  , vs),  , usVs' as ((root (def c',  , s'),  , s'),  , vs'),  , p',  , sc) if eqCid (c,  , c') then eqSpineIL (gQ,  , d,  , d',  , ((s,  , s),  , (constType c,  , id)),  , ((s',  , s'),  , (constType c',  , id)),  , p',  , sc) else (if ! chatter > 4 then print (" Proved: " ^ atomicRCtxToString (g,  , (eq (usVs,  , usVs') :: d)) ^ atomicRCtxToString (g,  , d') ^ " ---> " ^ atomicPredToString (g,  , p') ^ "\n") else (); true) eqIL(gQ as (g,  , q),  , d,  , d',  , (us as (root (const c,  , s),  , s),  , vs),  , (us' as (root (bVar n,  , s'),  , s'),  , vs'),  , p',  , sc) if isAtomic (gQ,  , us') then leftInstantiate (gQ,  , d,  , (eq ((us',  , vs'),  , (us,  , vs)) :: d'),  , p',  , sc) else (if ! chatter > 4 then print (" Proved: " ^ atomicRCtxToString (g,  , (eq ((us,  , vs),  , (us',  , vs')) :: d)) ^ atomicRCtxToString (g,  , d') ^ " ---> " ^ atomicPredToString (g,  , p') ^ "\n") else (); true) eqIL(gQ as (g,  , q),  , d,  , d',  , (us as (root (def c,  , s),  , s),  , vs),  , (us' as (root (bVar n,  , s'),  , s'),  , vs'),  , p',  , sc) if isAtomic (gQ,  , us') then leftInstantiate (gQ,  , d,  , (eq ((us',  , vs'),  , (us,  , vs)) :: d'),  , p',  , sc) else (if ! chatter > 4 then print (" Proved: " ^ atomicRCtxToString (g,  , (eq ((us,  , vs),  , (us',  , vs')) :: d)) ^ atomicRCtxToString (g,  , d') ^ " ---> " ^ atomicPredToString (g,  , p') ^ "\n") else (); true) eqIL(gQ as (g,  , q),  , d,  , d',  , (us as (root (bVar n,  , s),  , s),  , vs),  , (us' as (root (def c,  , s'),  , s'),  , vs'),  , p',  , sc) if isAtomic (gQ,  , us) then leftInstantiate (gQ,  , d,  , (eq ((us,  , vs),  , (us',  , vs')) :: d'),  , p',  , sc) else (if ! chatter > 4 then print (" Proved: " ^ atomicRCtxToString (g,  , (eq ((us,  , vs),  , (us',  , vs')) :: d')) ^ atomicRCtxToString (g,  , d') ^ " ---> " ^ atomicPredToString (g,  , p') ^ "\n") else (); true) eqIL(gQ as (g,  , q),  , d,  , d',  , (us as (root (bVar n,  , s),  , s),  , vs),  , (us' as (root (const c,  , s'),  , s'),  , vs'),  , p',  , sc) if isAtomic (gQ,  , us) then leftInstantiate (gQ,  , d,  , (eq ((us,  , vs),  , (us',  , vs')) :: d'),  , p',  , sc) else (if ! chatter > 4 then print (" Proved: " ^ atomicRCtxToString (g,  , (eq ((us,  , vs),  , (us',  , vs')) :: d')) ^ atomicRCtxToString (g,  , d') ^ " ---> " ^ atomicPredToString (g,  , p') ^ "\n") else (); true) eqIL(gQ as (g,  , q),  , d,  , d',  , (us as (root (bVar n,  , s),  , s),  , vs),  , (us' as (root (bVar n',  , s'),  , s'),  , vs'),  , p',  , sc) if (n = n') then let let  in in eqSpineIL (gQ,  , d,  , d',  , ((s,  , s),  , (v',  , id)),  , ((s',  , s'),  , (v',  , id)),  , p',  , sc) else leftInstantiate (gQ,  , d,  , (eq ((us,  , vs),  , (us',  , vs')) :: d'),  , p',  , sc) eqIL(gQ as (g,  , q),  , d,  , d',  , usVs,  , usVs',  , p',  , sc) (if ! chatter > 4 then print (" Proved: " ^ atomicRCtxToString (g,  , (eq ((usVs),  , (usVs')) :: d)) ^ atomicRCtxToString (g,  , d') ^ " ---> " ^ atomicPredToString (g,  , p') ^ "\n") else (); true) eqSpineIL(gQ,  , d,  , d',  , (ss,  , vs),  , (ss',  , vs'),  , p',  , sc) eqSpineILW (gQ,  , d,  , d',  , (ss,  , whnf vs),  , (ss',  , whnf vs'),  , p',  , sc) eqSpineILW(gQ,  , d,  , d',  , ((nil,  , s),  , vs),  , ((nil,  , s'),  , vs'),  , p',  , sc) leftInstantiate (gQ,  , d,  , d',  , p',  , sc) eqSpineILW(gQ,  , d,  , d',  , ((sClo (s,  , s'),  , s''),  , vs),  , ssVs',  , p',  , sc) eqSpineIL (gQ,  , d,  , d',  , ((s,  , comp (s',  , s'')),  , vs),  , ssVs',  , p',  , sc) eqSpineILW(gQ,  , d,  , d',  , ssVs,  , ((sClo (s',  , s'),  , s''),  , vs'),  , p',  , sc) eqSpineIL (gQ,  , d,  , d',  , ssVs,  , ((s',  , comp (s',  , s'')),  , vs'),  , p',  , sc) eqSpineILW(gQ,  , d,  , d',  , ((app (u,  , s),  , s1),  , (pi ((dec (_,  , v1),  , _),  , v2),  , s2)),  , ((app (u',  , s'),  , s1'),  , (pi ((dec (_,  , v1'),  , _),  , v2'),  , s2')),  , p',  , sc) let let  in in eqSpineIL (gQ,  , d1,  , d',  , ((s,  , s1),  , (v2,  , dot (exp (eClo (u,  , s1)),  , s2))),  , ((s',  , s1'),  , (v2',  , dot (exp (eClo (u',  , s1')),  , s2'))),  , p',  , sc)(*--------------------------------------------------------------*)
(* rightDecompose (GQ, D', P) = B

    B iff
        G : Q
    and D is maximally unfolded, but does not contain any EVars
    and P is a order relation
    and G |- P
    and D --> P

    *)
 rightDecompose(gQ,  , d',  , less (o,  , o')) ordLtR (gQ,  , d',  , o,  , o') rightDecompose(gQ,  , d',  , leq (o,  , o')) ordLeR (gQ,  , d',  , o,  , o') rightDecompose(gQ,  , d',  , eq (o,  , o')) ordEqR (gQ,  , d',  , o,  , o')(* ordLtR (GQ, D, O1, O2) = B'

       Invariant:
       If   G : Q
       and  G |- O1 augmented subterm
       and  G |- O2 augmented subterm not containing any EVars
       then B' holds iff D --> O1 < O2
    *)
 ordLtR(gQ,  , d',  , arg usVs,  , arg usVs') ltAtomicR (gQ,  , d',  , usVs,  , usVs',  , init,  , leftInstantiate) ordLtR(gQ,  , d',  , lex o,  , lex o') ltLexR (gQ,  , d',  , o,  , o') ordLtR(gQ,  , d',  , simul o,  , simul o') ltSimulR (gQ,  , d',  , o,  , o')(* ordLeR (GQ, D, O1, O2) = B'

       Invariant:
       If   G : Q
       and  G |- O1 augmented subterm
       and  G |- O2 augmented subterm not containing any EVars
       then B' holds iff D --> O1 <= O2
    *)
 ordLeR(gQ,  , d',  , arg usVs,  , arg usVs') leAtomicR (gQ,  , d',  , usVs,  , usVs',  , init,  , leftInstantiate) ordLeR(gQ,  , d',  , lex o,  , lex o') ltLexR (gQ,  , d',  , o,  , o') || ordEqsR (gQ,  , d',  , o,  , o') ordLeR(gQ,  , d',  , simul o,  , simul o') leSimulR (gQ,  , d',  , o,  , o')(* ordEqR (GQ, D, O1, O2) = B'

       Invariant:
       If   G : Q
       and  G |- O1 augmented subterm
       and  G |- O2 augmented subterm not containing any EVars
       then B' holds iff D --> O1 = O2
    *)
 ordEqR(gQ,  , d',  , arg usVs,  , arg usVs') conv (usVs,  , usVs') || eqAtomicR (gQ,  , d',  , usVs,  , usVs',  , init,  , leftInstantiate) ordEqR(gQ,  , d',  , lex o,  , lex o') ordEqsR (gQ,  , d',  , o,  , o') ordEqR(gQ,  , d',  , simul o,  , simul o') ordEqsR (gQ,  , d',  , o,  , o')(* ordEqsR (GQ, D', L1, L2) = B'

       Invariant:
       If   G : Q
       and  G |- L1 list of augmented subterms
       and  G |- L2 list of augmented subterms not containing any EVars
       then B' holds iff D' --> L1 = L2
    *)
 ordEqsR(gQ,  , d',  , nil,  , nil) true ordEqsR(gQ,  , d',  , o :: l,  , o' :: l') ordEqR (gQ,  , d',  , o,  , o') && ordEqsR (gQ,  , d',  , l,  , l')(* ltLexR (GQ, D', L1, L2) = B'

       Invariant:
       If   G : Q
       and  G |- L1 list of augmented subterms
       and  G |- L2 list of augmented subterms not contianing any EVars
       then B' holds iff D' --> L1 is lexically smaller than L2
    *)
 ltLexR(gQ,  , d',  , nil,  , nil) false ltLexR(gQ,  , d',  , o :: l,  , o' :: l') ordLtR (gQ,  , d',  , o,  , o') || (ordEqR (gQ,  , d',  , o,  , o') && ltLexR (gQ,  , d',  , l,  , l')) leLexR(gQ,  , d',  , l,  , l') ltLexR (gQ,  , d',  , l,  , l') || ordEqsR (gQ,  , d',  , l,  , l')(* ltSimulR (GQ, D, L1, L2) = B'

       Invariant:
       If   G : Q
       and  G |- L1 list of augmented subterms
       and  G |- L2 list of augmented subterms not contianing any EVars
       then B' holds iff D implies that L1 is simultaneously smaller than L2
    *)
 ltSimulR(gQ,  , d,  , nil,  , nil) false ltSimulR(gQ,  , d,  , o :: l,  , o' :: l') (ordLtR (gQ,  , d,  , o,  , o') && leSimulR (gQ,  , d,  , l,  , l')) || (ordEqR (gQ,  , d,  , o,  , o') && ltSimulR (gQ,  , d,  , l,  , l'))(* leSimulR (G, Q, L1, L2) = B'

       Invariant:
       If   G : Q
       and  G |- L1 list of augmented subterms
       and  G |- L2 list of augmented subterms not containing any EVars
       then B' holds iff D implies that L1 is simultaneously less than or equal to L2
    *)
 leSimulR(gQ,  , d,  , nil,  , nil) true leSimulR(gQ,  , d,  , o :: l,  , o' :: l') ordLeR (gQ,  , d,  , o,  , o') && leSimulR (gQ,  , d,  , l,  , l')(*--------------------------------------------------------------*)
(* Atomic Orders (Right) *)
(* ltAtomicR (GQ, (D, D'), UsVs, UsVs', sc, k) = B
     Invariant:
       B' holds  iff
            G : Q
       and  G |- s1 : G1   G1 |- U : V1
       and  G |- s2 : G2   G2 |- V : L
       and  G |- U[s1] : V[s2]
       and  G |- s1' : G3   G3 |- U' : V1'
       and  G |- s2' : G4   G4 |- V' : L
       and  G |- U'[s1'] : V'[s2']
       and  D' implies U[s1] is a strict subterm of U'[s1']
       and  sc is a constraint continuation representing restrictions on EVars
       and only U'[s'] contains EVars
       and k is a continuation describing what happens when
           UsVs and UsVs' are maximally unfolded
    *)
 ltAtomicR(gQ,  , d,  , usVs,  , usVs',  , sc,  , k) ltAtomicRW (gQ,  , d,  , whnfEta usVs,  , usVs',  , sc,  , k) ltAtomicRW(gQ,  , d,  , usVs as (us,  , vs as (root _,  , s')),  , usVs',  , sc,  , k) ltR (gQ,  , d,  , usVs,  , usVs',  , sc,  , k) ltAtomicRW(gQ as (g,  , q),  , d,  , ((lam (_,  , u),  , s1),  , (pi ((dec,  , _),  , v),  , s2)),  , ((u',  , s1'),  , (v',  , s2')),  , sc,  , k) let let  inlet  inlet  in in ltAtomicR ((decl (g,  , decLUName (g,  , decSub (dec,  , s2))),  , decl (q,  , all)),  , d',  , usVs,  , usVs',  , sc,  , k)(* leAtomicR (GQ, D, UsVs, UsVs', sc, k) = B
     Invariant:
       B' holds  iff
            G : Q
       and  G |- s1 : G1   G1 |- U : V1
       and  G |- s2 : G2   G2 |- V : L
       and  G |- U[s1] : V[s2]
       and  G |- s1' : G3   G3 |- U' : V1'
       and  G |- s2' : G4   G4 |- V' : L
       and  G |- U'[s1'] : V'[s2']
       and  D implies U[s1] is a subterm of U'[s1']
       and  sc is a constraint continuation representing restrictions on EVars
       and only U'[s'] contains EVars
       and k is a continuation describing what happens when
           UsVs and UsVs' are maximally unfolded
    *)
 leAtomicR(gQ,  , d,  , usVs,  , usVs',  , sc,  , k) leAtomicRW (gQ,  , d,  , whnfEta usVs,  , usVs',  , sc,  , k) leAtomicRW(gQ,  , d,  , usVs as (us,  , vs as (root _,  , s')),  , usVs',  , sc,  , k) leR (gQ,  , d,  , usVs,  , usVs',  , sc,  , k) leAtomicRW(gQ as (g,  , q),  , d,  , ((lam (_,  , u),  , s1),  , (pi ((dec,  , _),  , v),  , s2)),  , ((u',  , s1'),  , (v',  , s2')),  , sc,  , k) let let  inlet  inlet  in in leAtomicR ((decl (g,  , decLUName (g,  , decSub (dec,  , s2))),  , decl (q,  , all)),  , d',  , usVs,  , usVs',  , sc,  , k)(* eqAtomicR (GQ, D, UsVs, UsVs', sc, k) = B
     Invariant:
       B' holds  iff
            G : Q
       and  G |- s1 : G1   G1 |- U : V1
       and  G |- s2 : G2   G2 |- V : L
       and  G |- U[s1] : V[s2]
       and  G |- s1' : G3   G3 |- U' : V1'
       and  G |- s2' : G4   G4 |- V' : L
       and  G |- U'[s1'] : V'[s2']
       and  D implies U[s1] is structurally equivalent to U'[s1']
       and  sc is a constraint continuation representing restrictions on EVars
       and only U'[s'] contains EVars
       and k is a continuation describing what happens when
           UsVs and UsVs' are maximally unfolded
    *)
 eqAtomicR(gQ as (g,  , q),  , d,  , usVs,  , usVs',  , sc,  , k) eqAtomicRW (gQ,  , d,  , whnfEta usVs,  , whnfEta usVs',  , sc,  , k) eqAtomicRW(gQ as (g,  , q),  , d,  , ((lam (_,  , u),  , s1),  , (pi ((dec,  , _),  , v),  , s2)),  , ((lam (_,  , u'),  , s1'),  , (pi ((dec',  , _),  , v'),  , s2')),  , sc,  , k) eqAtomicR ((decl (g,  , decLUName (g,  , decSub (dec,  , s2))),  , decl (q,  , all)),  , shiftACtx d (fun s -> comp (s,  , shift)),  , ((u,  , dot1 s1'),  , (v,  , dot1 s2')),  , ((u',  , dot1 s1'),  , (v',  , dot1 s2')),  , sc,  , k) eqAtomicRW(gQ,  , d,  , (us,  , vs as (root _,  , s2)),  , (us',  , vs' as (root _,  , s2')),  , sc,  , k) eqR (gQ,  , d,  , (us,  , vs),  , (us',  , vs'),  , sc,  , k) eqAtomicRW(gQ,  , d,  , (us,  , vs),  , (us',  , vs'),  , sc,  , k) false(* ltR (GQ, D, UsVs, UsVs', sc, k) = B

       Invariant:
       B' holds  iff
            G : Q
       and  G |- s1 : G1   G1 |- U : V1
       and  G |- s2 : G2   G2 |- V : L
       and  G |- U[s1] : V[s2]
       and  G |- s1' : G3   G3 |- U' : V1'
       and  G |- s2' : G4   G4 |- V' : L
       and  G |- U'[s1'] : V'[s2']
       and  D' --> U[s1] is a strict subterm of U'[s1']
       and  sc is a constraint continuation representing restrictions on EVars
       and only U'[s'] contains EVars
       and U'[s'] will be maximally unfolded
       and k is a continuation describing what happens when
           UsVs and UsVs' are maximally unfolded

    *)
 ltR(gQ as (g,  , q),  , d,  , usVs,  , usVs',  , sc,  , k) ltRW (gQ,  , d,  , usVs,  , whnfEta usVs',  , sc,  , k) ltRW(gQ,  , d,  , (us,  , vs),  , (us' as (root (const c,  , s'),  , s'),  , vs'),  , sc,  , k) if isAtomic (gQ,  , us') then k (gQ,  , d,  , nil,  , less ((us,  , vs),  , (us',  , vs')),  , sc)(* either leftInstantiate D or  atomic reasoning *)
 else ltSpineR (gQ,  , d,  , (us,  , vs),  , ((s',  , s'),  , (constType c,  , id)),  , sc,  , k) ltRW(gQ,  , d,  , (us,  , vs),  , (us' as (root (def c,  , s'),  , s'),  , vs'),  , sc,  , k) if isAtomic (gQ,  , us') then k (gQ,  , d,  , nil,  , less ((us,  , vs),  , (us',  , vs')),  , sc)(* either leftInstantiate D or  atomic reasoning *)
 else ltSpineR (gQ,  , d,  , (us,  , vs),  , ((s',  , s'),  , (constType c,  , id)),  , sc,  , k) ltRW(gQ as (g,  , q),  , d,  , (us,  , vs),  , (us' as (root (bVar n,  , s'),  , s'),  , vs'),  , sc,  , k) if isAtomic (gQ,  , us') then k (gQ,  , d,  , nil,  , less ((us,  , vs),  , (us',  , vs')),  , sc)(* either leftInstantiate D or  atomic reasoning *)
 else let let  in in ltSpineR (gQ,  , d,  , (us,  , vs),  , ((s',  , s'),  , (v',  , id)),  , sc,  , k) ltRW(gQ,  , d,  , _,  , ((eVar _,  , _),  , _),  , _,  , _) false ltRW(gQ as (g,  , q),  , d,  , ((u,  , s1),  , (v,  , s2)),  , ((lam (dec (_,  , v1'),  , u'),  , s1'),  , (pi ((dec (_,  , v2'),  , _),  , v'),  , s2')),  , sc,  , k) if equiv (targetFam v,  , targetFam v1')(* == I.targetFam V2' *)
 then let (* enforce that X is only instantiated to parameters *)
let  in(* = I.newEVar (I.EClo (V2', s2')) *)
let  in in ltR (gQ,  , d,  , ((u,  , s1),  , (v,  , s2)),  , ((u',  , dot (exp (x),  , s1')),  , (v',  , dot (exp (x),  , s2'))),  , sc',  , k) else if below (targetFam v1',  , targetFam v) then let let  in(* = I.newEVar (I.EClo (V2', s2')) *)
 in ltR (gQ,  , d,  , ((u,  , s1),  , (v,  , s2)),  , ((u',  , dot (exp (x),  , s1')),  , (v',  , dot (exp (x),  , s2'))),  , sc,  , k) else false(* possibly redundant if lhs always subordinate to rhs *)
 ltSpineR(gQ,  , d,  , (us,  , vs),  , (ss',  , vs'),  , sc,  , k) ltSpineRW (gQ,  , d,  , (us,  , vs),  , (ss',  , whnf vs'),  , sc,  , k) ltSpineRW(gQ,  , d,  , (us,  , vs),  , ((nil,  , _),  , _),  , _,  , _) false ltSpineRW(gQ,  , d,  , (us,  , vs),  , ((sClo (s,  , s'),  , s''),  , vs'),  , sc,  , k) ltSpineR (gQ,  , d,  , (us,  , vs),  , ((s,  , comp (s',  , s'')),  , vs'),  , sc,  , k) ltSpineRW(gQ,  , d,  , (us,  , vs),  , ((app (u',  , s'),  , s1'),  , (pi ((dec (_,  , v1'),  , _),  , v2'),  , s2')),  , sc,  , k) leAtomicR (gQ,  , d,  , (us,  , vs),  , ((u',  , s1'),  , (v1',  , s2')),  , sc,  , k) || ltSpineR (gQ,  , d,  , (us,  , vs),  , ((s',  , s1'),  , (v2',  , dot (exp (eClo (u',  , s1')),  , s2'))),  , sc,  , k)(* leR (GQ, D, UsVs, UsVs', sc, k) = B

       Invariant:
       B' holds  iff
            G : Q
       and  G |- s1 : G1   G1 |- U : V1
       and  G |- s2 : G2   G2 |- V : L
       and  G |- U[s1] : V[s2]
       and  G |- s1' : G3   G3 |- U' : V1'
       and  G |- s2' : G4   G4 |- V' : L
       and  G |- U'[s1'] : V'[s2']
       and  D' --> U[s1] is a subterm of U'[s1']
       and  sc is a constraint continuation representing restrictions on EVars
       and only U'[s'] contains EVars
       and U'[s'] will be maximally unfolded
    *)
 leR(gQ,  , d,  , usVs,  , usVs',  , sc,  , k) leRW (gQ,  , d,  , usVs,  , whnfEta usVs',  , sc,  , k) leRW(gQ as (g,  , q),  , d,  , ((u,  , s1),  , (v,  , s2)),  , ((lam (dec (_,  , v1'),  , u'),  , s1'),  , (pi ((dec (_,  , v2'),  , _),  , v'),  , s2')),  , sc,  , k) if equiv (targetFam v,  , targetFam v1')(* == I.targetFam V2' *)
 then let let  in(* = I.newEVar (I.EClo (V2', s2')) *)
(* enforces that X can only bound to parameter or remain uninstantiated *)
let  in in leR (gQ,  , d,  , ((u,  , s1),  , (v,  , s2)),  , ((u',  , dot (exp (x),  , s1')),  , (v',  , dot (exp (x),  , s2'))),  , sc',  , k) else if below (targetFam v1',  , targetFam v) then let let  in(* = I.newEVar (I.EClo (V2', s2')) *)
 in leR (gQ,  , d,  , ((u,  , s1),  , (v,  , s2)),  , ((u',  , dot (exp (x),  , s1')),  , (v',  , dot (exp (x),  , s2'))),  , sc,  , k) else false leRW(gQ,  , d,  , usVs,  , usVs',  , sc,  , k) ltR (gQ,  , d,  , usVs,  , usVs',  , sc,  , k) || eqR (gQ,  , d,  , usVs,  , usVs',  , sc,  , k)(* eqR (GQ, D, UsVs, UsVs', sc, k) = B

       Invariant:
       B' holds  iff
            G : Q
       and  G |- s1 : G1   G1 |- U : V1
       and  G |- s2 : G2   G2 |- V : L
       and  G |- U[s1] : V[s2]
       and  G |- s1' : G3   G3 |- U' : V1'
       and  G |- s2' : G4   G4 |- V' : L
       and  G |- U'[s1'] : V'[s2']
       and  D' --> U[s1] = U'[s1']
       and  sc is a constraint continuation representing restrictions on EVars
       and only U'[s'] contains EVars
       and U'[s'] will be maximally unfolded
    *)
 eqR(gQ as (g,  , q),  , d,  , usVs,  , usVs',  , sc,  , k) trail (fun () -> eq (g,  , usVs,  , usVs') && sc ()) || eqR' (gQ,  , d,  , usVs,  , usVs',  , sc,  , k) eqR'(gQ,  , d,  , (us,  , vs as (pi ((dec (_,  , v2'),  , _),  , v'),  , s2')),  , (us',  , vs' as (root _,  , s2'')),  , sc,  , k) false eqR'(gQ,  , d,  , (us,  , vs as (root _,  , s2')),  , (us',  , vs' as (pi ((dec (_,  , v2''),  , _),  , v''),  , s2'')),  , sc,  , k) false eqR'(gQ,  , d,  , usVs as ((root (const c,  , s),  , s),  , vs),  , usVs' as ((root (const c',  , s'),  , s'),  , vs'),  , sc,  , k) if eqCid (c,  , c') then eqSpineR (gQ,  , d,  , ((s,  , s),  , (constType c,  , id)),  , ((s',  , s'),  , (constType c',  , id)),  , sc,  , k) else false eqR'(gQ,  , d,  , (us as (root (const c,  , s),  , s),  , vs),  , (us' as (root (bVar n,  , s'),  , s'),  , vs'),  , sc,  , k) if isAtomic (gQ,  , us') then k (gQ,  , d,  , nil,  , eq ((us',  , vs'),  , (us,  , vs)),  , sc)(* either leftInstantiate D or atomic reasoning *)
 else false eqR'(gQ,  , d,  , (us as (root (bVar n,  , s),  , s),  , vs),  , (us' as (root (const c,  , s'),  , s'),  , vs'),  , sc,  , k) if isAtomic (gQ,  , us) then k (gQ,  , d,  , nil,  , eq ((us,  , vs),  , (us',  , vs')),  , sc)(* either leftInstantiate D or atomic reasoning *)
 else false eqR'(gQ,  , d,  , usVs as ((root (def c,  , s),  , s),  , vs),  , usVs' as ((root (def c',  , s'),  , s'),  , vs'),  , sc,  , k) if eqCid (c,  , c') then eqSpineR (gQ,  , d,  , ((s,  , s),  , (constType c,  , id)),  , ((s',  , s'),  , (constType c',  , id)),  , sc,  , k) else false eqR'(gQ,  , d,  , (us as (root (def c,  , s),  , s),  , vs),  , (us' as (root (bVar n,  , s'),  , s'),  , vs'),  , sc,  , k) if isAtomic (gQ,  , us') then k (gQ,  , d,  , nil,  , eq ((us',  , vs'),  , (us,  , vs)),  , sc)(* either leftInstantiate D or atomic reasoning *)
 else false eqR'(gQ,  , d,  , (us as (root (bVar n,  , s),  , s),  , vs),  , (us' as (root (def c,  , s'),  , s'),  , vs'),  , sc,  , k) if isAtomic (gQ,  , us) then k (gQ,  , d,  , nil,  , eq ((us,  , vs),  , (us',  , vs')),  , sc)(* either leftInstantiate D or atomic reasoning *)
 else false eqR'(gQ as (g,  , q),  , d,  , (us as (root (bVar n,  , s),  , s),  , vs),  , (us' as (root (bVar n',  , s'),  , s'),  , vs'),  , sc,  , k) if (n = n') then let let  in in eqSpineR (gQ,  , d,  , ((s,  , s),  , (v',  , id)),  , ((s',  , s'),  , (v',  , id)),  , sc,  , k) else k (gQ,  , d,  , nil,  , eq ((us,  , vs),  , (us',  , vs')),  , sc) eqR'(gQ,  , d,  , usVs,  , usVs',  , sc,  , k) k (gQ,  , d,  , nil,  , eq (usVs,  , usVs'),  , sc)(* either leftInstantiate D or atomic reasoning *)
 eqSpineR(gQ,  , d,  , (ss,  , vs),  , (ss',  , vs'),  , sc,  , k) eqSpineRW (gQ,  , d,  , (ss,  , (whnf vs)),  , (ss',  , (whnf vs')),  , sc,  , k) eqSpineRW(gQ,  , d,  , ((nil,  , s),  , vs),  , ((nil,  , s'),  , vs'),  , sc,  , k) true eqSpineRW(gQ,  , d,  , ((sClo (s,  , s'),  , s''),  , vs),  , ssVs',  , sc,  , k) eqSpineR (gQ,  , d,  , ((s,  , comp (s',  , s'')),  , vs),  , ssVs',  , sc,  , k) eqSpineRW(gQ,  , d,  , ssVs,  , ((sClo (s',  , s'),  , s''),  , vs'),  , sc,  , k) eqSpineR (gQ,  , d,  , ssVs,  , ((s',  , comp (s',  , s'')),  , vs'),  , sc,  , k) eqSpineRW(gQ,  , d,  , ((app (u,  , s),  , s1),  , (pi ((dec (_,  , v1),  , _),  , v2),  , s2)),  , ((app (u',  , s'),  , s1'),  , (pi ((dec (_,  , v1'),  , _),  , v2'),  , s2')),  , sc,  , k) eqAtomicR (gQ,  , d,  , ((u,  , s1),  , (v1,  , s2)),  , ((u',  , s1'),  , (v1',  , s2')),  , sc,  , k) && eqSpineR (gQ,  , d,  , ((s,  , s1),  , (v2,  , dot (exp (eClo (u,  , s1)),  , s2))),  , ((s',  , s1'),  , (v2',  , dot (exp (eClo (u',  , s1')),  , s2'))),  , sc,  , k) eqSpineRW(gQ,  , d,  , ssVs,  , ssVs',  , sc,  , k) false(*--------------------------------------------------------------*)
(* leftDecompose (G, Q, D, D', P) = B

      if G : Q and
         D --> P  where D might contain orders (lex and simul)

      then D' --> P
           where all orders in D' are atomic

      D' accumulates all orders which are maximally unfolded,
      but do not contain any EVars

      maximally unfolded orders not containing EVars are:

      Less: R < L

      L := Root(c, Nil) | Root(n, Nil)
      R := Root(c, S) | Root(n, S) | Lam(x:A, R)
      S := . | App(R, S)


      Eq : R = L
      R := Root(n, Nil) | Lam(x:A, R)
      L := Root(c, S) | Root(n, S) | Lam(x:A, R)
      S := . | App(R, S)

    *)
let rec leftDecompose(gQ as (g,  , q),  , nil,  , d',  , p) rightDecompose (gQ,  , d',  , p) leftDecompose(gQ,  , (less (arg usVs,  , arg usVs') :: d),  , d',  , p) ltAtomicL (gQ,  , d,  , d',  , usVs,  , usVs',  , p) leftDecompose(gQ,  , (less (lex o,  , lex o') :: d),  , d',  , p) ltLexL (gQ,  , d,  , d',  , o,  , o',  , p) leftDecompose(gQ,  , (less (simul o,  , simul o') :: d),  , d',  , p) ltSimulL (gQ,  , d,  , d',  , o,  , o',  , p) leftDecompose(gQ,  , (leq (arg usVs,  , arg usVs') :: d),  , d',  , p) leAtomicL (gQ,  , d,  , d',  , usVs,  , usVs',  , p) leftDecompose(gQ,  , (leq (lex o,  , lex o') :: d),  , d',  , p) leftDecompose (gQ,  , (less (lex o,  , lex o') :: d),  , d',  , p) && leftDecompose (gQ,  , (eq (lex o,  , lex o') :: d),  , d',  , p) leftDecompose(gQ,  , (leq (simul o,  , simul o') :: d),  , d',  , p) leSimulL (gQ,  , d,  , d',  , o,  , o',  , p) leftDecompose(gQ,  , (eq (arg usVs,  , arg usVs') :: d),  , d',  , p) eqAtomicL (gQ,  , d,  , d',  , usVs,  , usVs',  , p) leftDecompose(gQ,  , (eq (lex o,  , lex o') :: d),  , d',  , p) eqsL (gQ,  , d,  , d',  , o,  , o',  , p) leftDecompose(gQ,  , (eq (simul o,  , simul o') :: d),  , d',  , p) eqsL (gQ,  , d,  , d',  , o,  , o',  , p) leftDecompose(gQ as (g,  , q),  , (pi (dec,  , o) :: d),  , d',  , p) ((if ! chatter > 3 then (print " Ignoring quantified order "; print (makestring_fmt (fmtPredicate (g,  , pi (dec,  , o))))) else ()); leftDecompose (gQ,  , d,  , d',  , p))(*--------------------------------------------------------------*)
(* Lexicographic and Simultanous Orders (left)*)
(* If D, D', Lex O1, ....On < Lex O'1, ....O'n --> P
      then
            D, D', O1 < O1' --> P
        and D, D', O1 = O1', O2 < O2 --> P

        ...
        and D, D', O1 = O1', .., O_n-1 = O'_n-1, O_n < O'_n --> P
    *)
 ltLexL(gQ,  , d,  , d',  , nil,  , nil,  , p) true ltLexL(gQ,  , d,  , d',  , o :: l,  , o' :: l',  , p) leftDecompose (gQ,  , (less (o,  , o') :: d),  , d',  , p) && ltLexL (gQ,  , (eq (o,  , o') :: d),  , d',  , l,  , l',  , p)(* If D, D', Lex O1, ....On = Lex O'1, ....O'n --> P
      If D, D', Simul O1, ....On = Simul O'1, ....O'n --> P
      then
            D, D', O1 = O1' --> P
        and D, D', O2 = O2' --> P

        ...
        and D, D', On = On' --> P
    *)
 eqsL(gQ,  , d,  , d',  , nil,  , nil,  , p) true eqsL(gQ,  , d,  , d',  , o :: l,  , o' :: l',  , p) leftDecompose (gQ,  , (eq (o,  , o') :: d),  , d',  , p) && eqsL (gQ,  , d,  , d',  , l,  , l',  , p) ltSimulL(gQ,  , d,  , d',  , nil,  , nil,  , p) leftDecompose (gQ,  , d,  , d',  , p) ltSimulL(gQ,  , d,  , d',  , o :: l,  , o' :: l',  , p) leSimulL (gQ,  , (less (o,  , o') :: d),  , d',  , l,  , l',  , p) || ltSimulL (gQ,  , (eq (o,  , o') :: d),  , d',  , l,  , l',  , p) leSimulL(gQ,  , d,  , d',  , nil,  , nil,  , p) leftDecompose (gQ,  , d,  , d',  , p) leSimulL(gQ,  , d,  , d',  , o :: l,  , o' :: l',  , p) leSimulL (gQ,  , (leq (o,  , o') :: d),  , d',  , l,  , l',  , p)(*--------------------------------------------------------------*)
(* Atomic Orders (left) *)
(* U := Root(c, S) | Root(n, S) | Lam(x:A, U) *)
(* ltAtomicL (GQ as (G, Q), D, D', ((U, s1), (V, s2)), ((U', s1'), (V', s2')), P) = B

     B holds iff

            G : Q
       and  G |- s1 : G1   G1 |- U : V1
       and  G |- s2 : G2   G2 |- V : L
       and  G |- U[s1] : V[s2]
       and  G |- s1' : G3   G3 |- U' : V1'
       and  G |- s2' : G4   G4 |- V' : L
       and  G |- U'[s1'] : V'[s2']

       and  G |- D, D', (U[s1]:V[s2]) < U'[s1']:V'[s2']) --> P


       if G |- D, D', (Us:Vs) < (\x1:A1....\xn:An. U'[s1']: V'[s2']) --> P and
               (n >= 0)
       then
          G, a1:A1, .... an:An |-
             D^n, D'^n, (Us^n:Vs^n) < U'[a1... an . s1'^n]:V'[a1. ... . an . s2'^n] --> P^n

       where D^n, (Us^n, P^n) means all substitutions in D (U, P etc)
             are shifted by n
    *)
 ltAtomicL(gQ,  , d,  , d',  , usVs,  , usVs',  , p) ltAtomicLW (gQ,  , d,  , d',  , usVs,  , whnfEta usVs',  , p) ltAtomicLW(gQ as (g,  , q),  , d,  , d',  , usVs,  , (us',  , vs' as (root _,  , s')),  , p) ltL (gQ,  , d,  , d',  , usVs,  , (us',  , vs'),  , p) ltAtomicLW(gQ as (g,  , q),  , d,  , d',  , ((u,  , s1),  , (v,  , s2)),  , ((lam (_,  , u'),  , s1'),  , (pi ((dec',  , _),  , v'),  , s2')),  , p) let let  inlet  inlet  inlet  inlet  in in ltAtomicL ((decl (g,  , decLUName (g,  , decSub (dec',  , s2'))),  , decl (q,  , all)),  , d1,  , d1',  , usVs,  , usVs',  , p')(* see invariant for ltAtomic *)
 leAtomicL(gQ,  , d,  , d',  , usVs,  , usVs',  , p) leAtomicLW (gQ,  , d,  , d',  , usVs,  , whnfEta usVs',  , p) leAtomicLW(gQ,  , d,  , d',  , usVs,  , (us',  , vs' as (root (h,  , s),  , s')),  , p) leL (gQ,  , d,  , d',  , usVs,  , (us',  , vs'),  , p) leAtomicLW(gQ as (g,  , q),  , d,  , d',  , ((u,  , s1),  , (v,  , s2)),  , ((lam (_,  , u'),  , s1'),  , (pi ((dec',  , _),  , v'),  , s2')),  , p) let let  inlet  inlet  inlet  inlet  in in leAtomicL ((decl (g,  , decLUName (g,  , decSub (dec',  , s2'))),  , decl (q,  , all)),  , d1,  , d1',  , usVs,  , usVs',  , p')(*  *)
 eqAtomicL(gQ,  , d,  , d',  , usVs,  , usVs',  , p) eqAtomicLW (gQ,  , d,  , d',  , whnfEta usVs,  , whnfEta usVs',  , p) eqAtomicLW(gQ,  , d,  , d',  , (us,  , vs as (root _,  , s)),  , (us',  , vs' as (root _,  , s')),  , p) eqL (gQ,  , d,  , d',  , (us,  , vs),  , (us',  , vs'),  , p) eqAtomicLW(gQ,  , d,  , d',  , (us,  , vs as (root _,  , s)),  , (us',  , vs' as (pi _,  , s')),  , p) true eqAtomicLW(gQ,  , d,  , d',  , (us,  , vs as (pi _,  , s)),  , (us',  , vs' as (root _,  , s')),  , p) true eqAtomicLW(gQ,  , d,  , d',  , (us,  , vs as (pi _,  , s)),  , (us',  , vs' as (pi _,  , s')),  , p) leftDecompose (gQ,  , d,  , (eq ((us,  , vs),  , (us',  , vs')) :: d'),  , p)(*--------------------------------------------------------------*)
(* U' := Root(c, S) | Root(n, S) *)
(* add definitions! *)
 leL(gQ,  , d,  , d',  , usVs,  , usVs',  , p) ltAtomicL (gQ,  , d,  , d',  , usVs,  , usVs',  , p) && eqAtomicL (gQ,  , d,  , d',  , usVs,  , usVs',  , p)(*  If D, D', U < Root(c, S) --> P
      then D, D', U <= S' --> P
   *)
 ltL(gQ,  , d,  , d',  , usVs,  , (us',  , vs'),  , p) ltLW (gQ,  , d,  , d',  , usVs,  , (whnf us',  , vs'),  , p) ltLW(gQ as (g,  , q),  , d,  , d',  , usVs,  , (us' as (root (bVar n,  , s'),  , s'),  , vs'),  , p) if isAtomic (gQ,  , us') then leftDecompose (gQ,  , d,  , (less (usVs,  , (us',  , vs')) :: d'),  , p) else let let  in in ltSpineL (gQ,  , d,  , d',  , usVs,  , ((s',  , s'),  , (v',  , id)),  , p) ltLW(gQ,  , d,  , d',  , usVs,  , ((root (const c,  , s'),  , s'),  , vs'),  , p) ltSpineL (gQ,  , d,  , d',  , usVs,  , ((s',  , s'),  , (constType c,  , id)),  , p) ltLW(gQ,  , d,  , d',  , usVs,  , ((root (def c,  , s'),  , s'),  , vs'),  , p) ltSpineL (gQ,  , d,  , d',  , usVs,  , ((s',  , s'),  , (constType c,  , id)),  , p) ltSpineL(gQ,  , d,  , d',  , usVs,  , (ss',  , vs'),  , p) ltSpineLW (gQ,  , d,  , d',  , usVs,  , (ss',  , whnf vs'),  , p) ltSpineLW(gQ,  , d,  , d',  , usVs,  , ((nil,  , _),  , _),  , _) true ltSpineLW(gQ,  , d,  , d',  , usVs,  , ((sClo (s,  , s'),  , s''),  , vs'),  , p) ltSpineL (gQ,  , d,  , d',  , usVs,  , ((s,  , comp (s',  , s'')),  , vs'),  , p) ltSpineLW(gQ,  , d,  , d',  , usVs,  , ((app (u',  , s'),  , s1'),  , (pi ((dec (_,  , v1'),  , _),  , v2'),  , s2')),  , p) leAtomicL (gQ,  , d,  , d',  , usVs,  , ((u',  , s1'),  , (v1',  , s2')),  , p) && ltSpineL (gQ,  , d,  , d',  , usVs,  , ((s',  , s1'),  , (v2',  , dot (exp (eClo (u',  , s1')),  , s2'))),  , p)(*  eqL (GQ, D, D', UsVs, UsVs', P) = B

       B holds iff

            G : Q

       and  D is an Order relation ctx
       and  D' is an atomic order relation ctx
       and  P is a order relation

       and  G |- s1 : G1   G1 |- U : V1
       and  G |- s2 : G2   G2 |- V : L
       and  G |- U[s1] : V[s2]
       and  G |- s1' : G3   G3 |- U' : V1'
       and  G |- s2' : G4   G4 |- V' : L
       and  G |- U'[s1'] : V'[s2']

       and D, D', U[s1] = U'[s1'] --> P

       note: D, D', UsVs, UsVs' and P do not
             contain any EVars
   *)
 eqL(gQ,  , d,  , d',  , usVs,  , usVs',  , p) eqLW (gQ,  , d,  , d',  , whnfEta usVs,  , whnfEta usVs',  , p) eqLW(gQ,  , d,  , d',  , (us,  , vs as (pi ((dec (_,  , v2'),  , _),  , v'),  , s2')),  , (us',  , vs' as (pi ((dec (_,  , v2''),  , _),  , v''),  , s2'')),  , p) leftDecompose (gQ,  , d,  , (eq ((us,  , vs),  , (us',  , vs')) :: d'),  , p) eqLW(gQ,  , d,  , d',  , (us,  , vs as (pi ((dec (_,  , v2'),  , _),  , v'),  , s2')),  , (us',  , vs' as (root _,  , s2'')),  , p) true eqLW(gQ,  , d,  , d',  , (us,  , vs as (root _,  , s2')),  , (us',  , vs' as (pi ((dec (_,  , v2''),  , _),  , v''),  , s2'')),  , p) true eqLW(gQ,  , d,  , d',  , usVs as ((root (const c,  , s),  , s),  , vs),  , usVs' as ((root (const c',  , s'),  , s'),  , vs'),  , p) if eqCid (c,  , c') then eqSpineL (gQ,  , d,  , d',  , ((s,  , s),  , (constType c,  , id)),  , ((s',  , s'),  , (constType c',  , id)),  , p) else true eqLW(gQ,  , d,  , d',  , (us as (root (const c,  , s),  , s),  , vs),  , (us' as (root (bVar n,  , s'),  , s'),  , vs'),  , p) if isAtomic (gQ,  , us') then leftDecompose (gQ,  , d,  , (eq ((us',  , vs'),  , (us,  , vs)) :: d'),  , p) else true eqLW(gQ,  , d,  , d',  , (us as (root (bVar n,  , s),  , s),  , vs),  , (us' as (root (const c,  , s'),  , s'),  , vs'),  , p) if isAtomic (gQ,  , us) then leftDecompose (gQ,  , d,  , (eq ((us,  , vs),  , (us',  , vs')) :: d'),  , p) else true eqLW(gQ,  , d,  , d',  , usVs as ((root (def c,  , s),  , s),  , vs),  , usVs' as ((root (def c',  , s'),  , s'),  , vs'),  , p) if eqCid (c,  , c') then eqSpineL (gQ,  , d,  , d',  , ((s,  , s),  , (constType c,  , id)),  , ((s',  , s'),  , (constType c',  , id)),  , p) else true eqLW(gQ,  , d,  , d',  , (us as (root (def c,  , s),  , s),  , vs),  , (us' as (root (bVar n,  , s'),  , s'),  , vs'),  , p) if isAtomic (gQ,  , us') then leftDecompose (gQ,  , d,  , (eq ((us',  , vs'),  , (us,  , vs)) :: d'),  , p) else true eqLW(gQ,  , d,  , d',  , (us as (root (bVar n,  , s),  , s),  , vs),  , (us' as (root (def c,  , s'),  , s'),  , vs'),  , p) if isAtomic (gQ,  , us) then leftDecompose (gQ,  , d,  , (eq ((us,  , vs),  , (us',  , vs')) :: d'),  , p) else true eqLW(gQ as (g,  , q),  , d,  , d',  , (us as (root (bVar n,  , s),  , s),  , vs),  , (us' as (root (bVar n',  , s'),  , s'),  , vs'),  , p) if (n = n') then let let  in in eqSpineL (gQ,  , d,  , d',  , ((s,  , s),  , (v',  , id)),  , ((s',  , s'),  , (v',  , id)),  , p) else leftDecompose (gQ,  , d,  , (eq ((us,  , vs),  , (us',  , vs')) :: d'),  , p) eqLW(gQ,  , d,  , d',  , usVs,  , usVs',  , p) leftDecompose (gQ,  , d,  , (eq (usVs,  , usVs') :: d'),  , p) eqSpineL(gQ,  , d,  , d',  , (ss,  , vs),  , (ss',  , vs'),  , p) eqSpineLW (gQ,  , d,  , d',  , (ss,  , whnf vs),  , (ss',  , whnf vs'),  , p) eqSpineLW(gQ,  , d,  , d',  , ((nil,  , s),  , vs),  , ((nil,  , s'),  , vs'),  , p) leftDecompose (gQ,  , d,  , d',  , p) eqSpineLW(gQ,  , d,  , d',  , ((sClo (s,  , s'),  , s''),  , vs),  , ssVs',  , p) eqSpineL (gQ,  , d,  , d',  , ((s,  , comp (s',  , s'')),  , vs),  , ssVs',  , p) eqSpineLW(gQ,  , d,  , d',  , ssVs,  , ((sClo (s',  , s'),  , s''),  , vs'),  , p) eqSpineL (gQ,  , d,  , d',  , ssVs,  , ((s',  , comp (s',  , s'')),  , vs'),  , p) eqSpineLW(gQ,  , d,  , d',  , ((app (u,  , s),  , s1),  , (pi ((dec (_,  , v1),  , _),  , v2),  , s2)),  , ((app (u',  , s'),  , s1'),  , (pi ((dec (_,  , v1'),  , _),  , v2'),  , s2')),  , p) let let  in in eqSpineL (gQ,  , d1,  , d',  , ((s,  , s1),  , (v2,  , dot (exp (eClo (u,  , s1)),  , s2))),  , ((s',  , s1'),  , (v2',  , dot (exp (eClo (u',  , s1')),  , s2'))),  , p)(*--------------------------------------------------------------*)
(* Infer: D --> P *)
(* deduce (G, Q, D, P) = B

      B iff
         G :  Q
     and G |- D
     and G |- P
     and D implies P
    *)
let rec deduce(g,  , q,  , d,  , p) leftDecompose ((g,  , q),  , d,  , nil,  , p)let  inlet  inlet  in(* local *)
end