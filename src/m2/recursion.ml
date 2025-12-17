Recursion  Global GLOBAL    MetaSyn' METASYN    Whnf WHNF    Unify UNIFY    Conv CONV    Names NAMES    Subordinate SUBORDINATE    Print PRINT    Order ORDER    ModeTable MODETABLE    Lemma LEMMA    Lemma MetaSyn  MetaSyn'   Filling FILLING    Filling MetaSyn  MetaSyn'   MetaPrint METAPRINT    MetaPrint MetaSyn  MetaSyn'   MetaAbstract METAABSTRACT    MetaAbstract MetaSyn  MetaSyn'   Formatter FORMATTER     RECURSION  struct module exception type Operatormodule module module module module type Quantifier(*     | Ex                      *)
(* If Q marks all parameters in a context G we write   G : Q               *)
(* duplicate code? -fp *)
let rec vectorToString(g,  , o) let let rec fmtOrder(arg (us,  , vs)) [string (expToString (g,  , eClo us)); string ":"; string (expToString (g,  , eClo vs))] fmtOrder(lex l) [string "{"; hVbox (fmtOrders l); string "}"] fmtOrder(simul l) [string "["; hVbox (fmtOrders l); string "]"] fmtOrdersnil nil fmtOrders(o :: nil) fmtOrder o fmtOrders(o :: l) fmtOrder o @ (string " " :: fmtOrders l) in makestring_fmt (hVbox (fmtOrder o))(* vector (c, (S, s)) = P'

       Invariant:
       If   . |- c : V   G |- s : G'    G' |- S : V > type
       and  V = {x1:V1} ... {xn:Vn} type
       and  G |- S[s] = U1 .. Un : V[s] > type
       and  sel (c) = i1 .. im
       then P' = (U1'[s1']: V1'[t1'], .., U1'[sm']: V1'[tm'])
       and  G |- sj' : Gj'    Gj' |- Uj' : V1j'
       and  G |- tj' : Gj'    Gj' |- Vj' : L
       and  G |- Vj' [tj'] = V1j' [sj'] : L
       and  G |- Uik = Uk'[sk']
    *)
let rec vector(c,  , (s,  , s)) let let  inlet rec select'(n,  , (ss',  , vs'')) select'W (n,  , (ss',  , whnf vs'')) select'W(1,  , ((app (u',  , s'),  , s'),  , (pi ((dec (_,  , v''),  , _),  , _),  , s''))) ((u',  , s'),  , (v'',  , s'')) select'W(n,  , ((sClo (s',  , s1'),  , s2'),  , vs'')) select'W (n,  , ((s',  , comp (s1',  , s2')),  , vs'')) select'W(n,  , ((app (u',  , s'),  , s'),  , (pi ((dec (_,  , v1''),  , _),  , v2''),  , s''))) select' (n - 1,  , ((s',  , s'),  , (v2'',  , dot (exp (eClo (u',  , s')),  , s''))))let rec select(arg n) arg (select' (n,  , ((s,  , s),  , vid))) select(lex l) lex (map select l) select(simul l) simul (map select l) in select (selLookup c)(* set_parameter (G, X, k, sc, ops) = ops'

       Invariant:
       appends a list of recursion operators to ops after
       instantiating X with all possible local parameters (between 1 and k)
    *)
let rec set_parameter(g,  , x as eVar (r,  , _,  , v,  , _),  , k,  , sc,  , ops) let let rec set_parameter'(0,  , ops') ops' set_parameter'(k',  , ops') let let  inlet  in in set_parameter' (k' - 1,  , ops'') in set_parameter' (k,  , ops)(* ltinit (G, k, ((U1, s1), (V2, s2)), ((U3, s3), (V4, s4)), sc, ops) = ops'

       Invariant:
       If   G = G0, Gp    (G0, global context, Gp, parameter context)
       and  |Gp| = k
       and  G |- s1 : G1   G1 |- U1 : V1
       and  G |- s2 : G2   G2 |- V2 : L
            G |- s3 : G1   G1 |- U3 : V3
       and  G |- s4 : G2   G2 |- V4 : L
       and  G |- V1[s1] == V2 [s2]
       and  G |- V3[s3] == V4 [s5]
       and  ops is a set of all all possible states
       and  sc is success continuation
       then ops' is an extension of ops, containing all
            recursion operators
    *)
let rec ltinit(g,  , k,  , (us,  , vs),  , usVs',  , sc,  , ops) ltinitW (g,  , k,  , whnfEta (us,  , vs),  , usVs',  , sc,  , ops) ltinitW(g,  , k,  , (us,  , vs as (root _,  , _)),  , usVs',  , sc,  , ops) lt (g,  , k,  , (us,  , vs),  , usVs',  , sc,  , ops) ltinitW(g,  , k,  , ((lam (d1,  , u),  , s1),  , (pi (d2,  , v),  , s2)),  , ((u',  , s1'),  , (v',  , s2')),  , sc,  , ops) ltinit (decl (g,  , decSub (d1,  , s1), (* = I.decSub (D2, s2) *)
),  , k + 1,  , ((u,  , dot1 s1),  , (v,  , dot1 s2)),  , ((u',  , comp (s1',  , shift)),  , (v',  , comp (s2',  , shift))),  , sc,  , ops)(* lt (G, k, ((U, s1), (V, s2)), (U', s'), sc, ops) = ops'

       Invariant:
       If   G = G0, Gp    (G0, global context, Gp, parameter context)
       and  |Gp| = k
       and  G |- s1 : G1   G1 |- U1 : V1   (U1 [s1] in  whnf)
       and  G |- s2 : G2   G2 |- V2 : L    (V2 [s2] in  whnf)
            G |- s3 : G1   G1 |- U3 : V3
       and  G |- s4 : G2   G2 |- V4 : L
       and  k is the length of the local context
       and  G |- V1[s1] == V2 [s2]
       and  G |- V3[s3] == V4 [s5]
       and  ops is a set of already calculuate possible states
       and  sc is success continuation
       then ops' is an extension of ops, containing all
            recursion operators
    *)
(* Vs is Root!!! *)
(* (Us',Vs') may not be eta-expanded!!! *)
 lt(g,  , k,  , (us,  , vs),  , (us',  , vs'),  , sc,  , ops) ltW (g,  , k,  , (us,  , vs),  , whnfEta (us',  , vs'),  , sc,  , ops) ltW(g,  , k,  , (us,  , vs),  , ((root (const c,  , s'),  , s'),  , vs'),  , sc,  , ops) ltSpine (g,  , k,  , (us,  , vs),  , ((s',  , s'),  , (constType c,  , id)),  , sc,  , ops) ltW(g,  , k,  , (us,  , vs),  , ((root (bVar n,  , s'),  , s'),  , vs'),  , sc,  , ops) if n <= k then (* n must be a local variable *)
let let  in in ltSpine (g,  , k,  , (us,  , vs),  , ((s',  , s'),  , (v',  , id)),  , sc,  , ops) else ops ltW(g,  , _,  , _,  , ((eVar _,  , _),  , _),  , _,  , ops) ops ltW(g,  , k,  , ((u,  , s1),  , (v,  , s2)),  , ((lam (d as dec (_,  , v1'),  , u'),  , s1'),  , (pi ((dec (_,  , v2'),  , _),  , v'),  , s2')),  , sc,  , ops) if equiv (targetFam v,  , targetFam v1')(* == I.targetFam V2' *)
 then let (* enforce that X gets only bound to parameters *)
let  in(* = I.newEVar (I.EClo (V2', s2')) *)
let  in in lt (g,  , k,  , ((u,  , s1),  , (v,  , s2)),  , ((u',  , dot (exp (x),  , s1')),  , (v',  , dot (exp (x),  , s2'))),  , sc',  , ops) else if below (targetFam v1',  , targetFam v) then let let  in(* = I.newEVar (I.EClo (V2', s2')) *)
 in lt (g,  , k,  , ((u,  , s1),  , (v,  , s2)),  , ((u',  , dot (exp (x),  , s1')),  , (v',  , dot (exp (x),  , s2'))),  , sc,  , ops) else ops ltSpine(g,  , k,  , (us,  , vs),  , (ss',  , vs'),  , sc,  , ops) ltSpineW (g,  , k,  , (us,  , vs),  , (ss',  , whnf vs'),  , sc,  , ops) ltSpineW(g,  , k,  , (us,  , vs),  , ((nil,  , _),  , _),  , _,  , ops) ops ltSpineW(g,  , k,  , (us,  , vs),  , ((sClo (s,  , s'),  , s''),  , vs'),  , sc,  , ops) ltSpineW (g,  , k,  , (us,  , vs),  , ((s,  , comp (s',  , s'')),  , vs'),  , sc,  , ops) ltSpineW(g,  , k,  , (us,  , vs),  , ((app (u',  , s'),  , s1'),  , (pi ((dec (_,  , v1'),  , _),  , v2'),  , s2')),  , sc,  , ops) let let  in in ltSpine (g,  , k,  , (us,  , vs),  , ((s',  , s1'),  , (v2',  , dot (exp (eClo (u',  , s1')),  , s2'))),  , sc,  , ops')(* eq (G, ((U, s1), (V, s2)), (U', s'), sc, ops) = ops'

       Invariant:
       If   G |- s1 : G1   G1 |- U1 : V1   (U1 [s1] in  whnf)
       and  G |- s2 : G2   G2 |- V2 : L    (V2 [s2] in  whnf)
            G |- s3 : G1   G1 |- U3 : V3
       and  G |- s4 : G2   G2 |- V4 : L
       and  G |- V1[s1] == V2 [s2]
       and  G |- V3[s3] == V4 [s5]
       and  ops is a set of already calculuated possible states
       and  sc is success continuation
       then ops' is an extension of ops, containing all
            recursion operators resulting from U[s1] = U'[s']
    *)
 eq(g,  , (us,  , vs),  , (us',  , vs'),  , sc,  , ops) (trail (fun () -> if unifiable (g,  , vs,  , vs') && unifiable (g,  , us,  , us') then sc ops else ops))(* le (G, k, ((U, s1), (V, s2)), (U', s'), sc, ops) = ops'

       Invariant:
       If   G = G0, Gp    (G0, global context, Gp, parameter context)
       and  |Gp| = k
       and  G |- s1 : G1   G1 |- U1 : V1   (U1 [s1] in  whnf)
       and  G |- s2 : G2   G2 |- V2 : L    (V2 [s2] in  whnf)
            G |- s3 : G1   G1 |- U3 : V3
       and  G |- s4 : G2   G2 |- V4 : L
       and  k is the length of the local context
       and  G |- V1[s1] == V2 [s2]
       and  G |- V3[s3] == V4 [s5]
       and  ops is a set of already calculuated possible states
       and  sc is success continuation
       then ops' is an extension of ops, containing all
            recursion operators resulting from U[s1] <= U'[s']
    *)
 le(g,  , k,  , (us,  , vs),  , (us',  , vs'),  , sc,  , ops) let let  in in leW (g,  , k,  , (us,  , vs),  , whnfEta (us',  , vs'),  , sc,  , ops') leW(g,  , k,  , ((u,  , s1),  , (v,  , s2)),  , ((lam (d as dec (_,  , v1'),  , u'),  , s1'),  , (pi ((dec (_,  , v2'),  , _),  , v'),  , s2')),  , sc,  , ops) if equiv (targetFam v,  , targetFam v1')(* == I.targetFam V2' *)
 then let let  in(* = I.newEVar (I.EClo (V2', s2')) *)
let  in(* enforces that X can only bound to parameter *)
 in le (g,  , k,  , ((u,  , s1),  , (v,  , s2)),  , ((u',  , dot (exp (x),  , s1')),  , (v',  , dot (exp (x),  , s2'))),  , sc',  , ops) else if below (targetFam v1',  , targetFam v) then let let  in(* = I.newEVar (I.EClo (V2', s2')) *)
 in le (g,  , k,  , ((u,  , s1),  , (v,  , s2)),  , ((u',  , dot (exp (x),  , s1')),  , (v',  , dot (exp (x),  , s2'))),  , sc,  , ops) else ops leW(g,  , k,  , (us,  , vs),  , (us',  , vs'),  , sc,  , ops) lt (g,  , k,  , (us,  , vs),  , (us',  , vs'),  , sc,  , ops)(* ordlt (G, O1, O2, sc, ops) = ops'

       Invariant:
       If   G |- O1 augmented subterms
       and  G |- O2 augmented subterms
       and  ops is a set of already calculuated possible states
       and  sc is success continuation
       then ops' is an extension of ops, containing all
            recursion operators of all instantiations of EVars s.t. O1 is
            lexicographically smaller than O2
    *)
let rec ordlt(g,  , arg usVs,  , arg usVs',  , sc,  , ops) ltinit (g,  , 0,  , usVs,  , usVs',  , sc,  , ops) ordlt(g,  , lex l,  , lex l',  , sc,  , ops) ordltLex (g,  , l,  , l',  , sc,  , ops) ordlt(g,  , simul l,  , simul l',  , sc,  , ops) ordltSimul (g,  , l,  , l',  , sc,  , ops)(* ordltLex (G, L1, L2, sc, ops) = ops'

       Invariant:
       If   G |- L1 list of augmented subterms
       and  G |- L2 list of augmented subterms
       and  ops is a set of already calculuated possible states
       and  sc is success continuation
       then ops' is an extension of ops, containing all
            recursion operators of all instantiations of EVars s.t. L1 is
            lexicographically less then L2
    *)
 ordltLex(g,  , nil,  , nil,  , sc,  , ops) ops ordltLex(g,  , o :: l,  , o' :: l',  , sc,  , ops) let let  in in ordeq (g,  , o,  , o',  , fun ops'' -> ordltLex (g,  , l,  , l',  , sc,  , ops''),  , ops')(* ordltSimul (G, L1, L2, sc, ops) = ops'

       Invariant:
       If   G |- L1 list of augmented subterms
       and  G |- L2 list of augmented subterms
       and  ops is a set of already calculuated possible states
       and  sc is success continuation
       then ops' is an extension of ops, containing all
            recursion operators of all instantiations of EVars s.t. L1 is
            simultaneously smaller than L2
    *)
 ordltSimul(g,  , nil,  , nil,  , sc,  , ops) ops ordltSimul(g,  , o :: l,  , o' :: l',  , sc,  , ops) let let  in in ordeq (g,  , o,  , o',  , fun ops' -> ordltSimul (g,  , l,  , l',  , sc,  , ops'),  , ops'')(* ordleSimul (G, L1, L2, sc, ops) = ops'

       Invariant:
       If   G |- L1 list of augmented subterms
       and  G |- L2 list of augmented subterms
       and  ops is a set of already calculuated possible states
       and  sc is success continuation
       then ops' is an extension of ops, containing all
            recursion operators of all instantiations of EVars s.t. L1 is
            simultaneously smaller than or equal to L2
    *)
 ordleSimul(g,  , nil,  , nil,  , sc,  , ops) sc ops ordleSimul(g,  , o :: l,  , o' :: l',  , sc,  , ops) ordle (g,  , o,  , o',  , fun ops' -> ordleSimul (g,  , l,  , l',  , sc,  , ops'),  , ops)(* ordeq (G, O1, O2, sc, ops) = ops'

       Invariant:
       If   G |- O1 augmented subterms
       and  G |- O2 augmented subterms
       and  ops is a set of already calculuated possible states
       and  sc is success continuation
       then ops' is an extension of ops, containing all
            recursion operators of all instantiations of EVars s.t. O1 is
            convertible to O2
    *)
 ordeq(g,  , arg (us,  , vs),  , arg (us',  , vs'),  , sc,  , ops) if unifiable (g,  , vs,  , vs') && unifiable (g,  , us,  , us') then sc ops else ops ordeq(g,  , lex l,  , lex l',  , sc,  , ops) ordeqs (g,  , l,  , l',  , sc,  , ops) ordeq(g,  , simul l,  , simul l',  , sc,  , ops) ordeqs (g,  , l,  , l',  , sc,  , ops)(* ordlteqs (G, L1, L2, sc, ops) = ops'

       Invariant:
       If   G |- L1 list of augmented subterms
       and  G |- L2 list of augmented subterms
       and  ops is a set of already calculuated possible states
       and  sc is success continuation
       then ops' is an extension of ops, containing all
            recursion operators of all instantiations of EVars s.t. L1 is
            convertible to L2
    *)
 ordeqs(g,  , nil,  , nil,  , sc,  , ops) sc ops ordeqs(g,  , o :: l,  , o' :: l',  , sc,  , ops) ordeq (g,  , o,  , o',  , fun ops' -> ordeqs (g,  , l,  , l',  , sc,  , ops'),  , ops)(* ordeq (G, O1, O2, sc, ops) = ops'

       Invariant:
       If   G |- O1 augmented subterms
       and  G |- O2 augmented subterms
       and  ops is a set of already calculuated possible states
       and  sc is success continuation
       then ops' is an extension of ops, containing all
1           recursion operators of all instantiations of EVars s.t. O1 is
            convertible to O2 or smaller than O2
    *)
 ordle(g,  , o,  , o',  , sc,  , ops) let let  in in ordlt (g,  , o,  , o',  , sc,  , ops')(* createEVars (G, M) = ((G', M'), s')

       Invariant:
       If   |- G ctx
       and  G |- M mtx
       then |- G' ctx
       and  G' |- M' mtx
       and  G' |- s' : G
    *)
let rec createEVars(prefix (null,  , null,  , null)) (prefix (null,  , null,  , null),  , id) createEVars(prefix (decl (g,  , d),  , decl (m,  , top),  , decl (b,  , b))) let let  in in (prefix (decl (g',  , decSub (d,  , s')),  , decl (m',  , top),  , decl (b',  , b)),  , dot1 s') createEVars(prefix (decl (g,  , dec (_,  , v)),  , decl (m,  , bot),  , decl (b,  , _))) let let  inlet  in in (prefix (g',  , m',  , b'),  , dot (exp (x),  , s'))(* select (G, (V, s)) = (G', (V1', s1'), (V2', s2'))

     Invariant:
     If   G |- s : G1   G1 |- V : type
     and  G |- V [s] = {V1} ... {Vn} a S
     then G' = G, V1 .. Vn
     and  G' |- s1' : G1'   G1' |- V1' : type
     and  G' |- s2' : G2'   G2' |- V2' : type
     and  G' |- V1' [s1'] = V1 [^n]
     and  G' |- V2' [s2'] = a S
    *)
let rec select(g,  , vs) selectW (g,  , (whnf vs)) selectW(g,  , (pi ((d as dec (_,  , v1),  , _),  , v2),  , s)) let let rec select'(g,  , (vs1,  , vs2)) selectW' (g,  , (vs1,  , whnf vs2)) selectW'(g,  , (vs1,  , vs2 as (root _,  , _))) (g,  , (vs1,  , vs2)) selectW'(g,  , ((v1,  , s1),  , (pi ((d,  , p),  , v2'),  , s2))) select' (decl (g,  , decSub (d,  , s2)),  , ((v1,  , comp (s1,  , shift)),  , (v2',  , dot1 s2))) in select' (decl (g,  , decSub (d,  , s)),  , ((v1,  , comp (s,  , shift)),  , (v2,  , dot1 s)))(* lemma (S, t, ops) = (G', P', P'', abstract', ops')

       Invariant:
       If   S state  (S = ((G, M), V)
                     |- G ctx
                     G |- M mtx
                     G |- V = {V1} ... {Vn} a S)
       and  S' state derived from S by an inductive call to t
       and  ops a list of operators
       then G is context, where all - variables are replaced by EVars in S'
       and  P' is induction variable vector of EVars in the inductive call
       and  P'' is induction variable vector of the theorem S.
       and  G' |- P' : (V1' .. Vn')
              (where  t : {W1} ..{Wm} b S, and Vi' are among W1 .. Wm)
       and  G'' |- P'' : (V1'' .. Vn'')
              (where  a : {W1} ..{Wm} b S, and Vi'' are among W1 .. Wm)

    *)
let rec lemma(s,  , t,  , ops) let let  inlet  inlet  in in (g'',  , vector (a1,  , (s1,  , s1)),  , vector (a2,  , (s2,  , s2)),  , fun ops' -> ((abstract (state (name,  , prefix (g',  , m',  , b'),  , eClo (v,  , s')))) :: ops'),  , ops)(* expandLazy' (S, L, ops) = ops'

       Invariant:
       If   S state
       and  L list of mutual recursive type families
       and  ops a list of operators
       then ops' extends ops by all operators
         representing inductive calls to theorems in L
    *)
let rec expandLazy'(s,  , empty,  , ops) ops expandLazy'(s,  , (lE (t,  , l)),  , ops) expandLazy' (s,  , l,  , ordle (lemma (s,  , t,  , ops))) expandLazy'(s,  , (lT (t,  , l)),  , ops) expandLazy' (s,  , l,  , ordlt (lemma (s,  , t,  , ops)))let rec recursionDepthv let let rec recursionDepth'(root _,  , n) n recursionDepth'(pi (_,  , v),  , n) recursionDepth' (v,  , n + 1) in recursionDepth' (v,  , 0)(* expandLazy S = ops'

       Invariant:
       If   S State
       then ops' a list of operations which cause a recursive call
         (only induction variables are instantiated)
    *)
let rec expandLazy(s as state (_,  , _,  , v)) if recursionDepth v > (! maxRecurse) then nil else expandLazy' (s,  , (mutLookup (targetFam v)),  , nil)(* inputConv ((V1, s1), (V2, s2)) = B

       Invariant:
       If  G |- s1 : G1   G1 |- V1 : L
       and G |- s2 : G2   G2 |- V2 : L
       and G |- V1[s1] = c1 ; S1
       and G |- V2[s2] = c2 ; S2
       then B' holds iff c1 =  c2 and V1[s1] ==+ V2[s2]   (convertible on + arguments of c1)
    *)
let rec inputConv(vs1,  , vs2) inputConvW (whnf vs1,  , whnf vs2) inputConvW((root (const c1,  , s1),  , s1),  , (root (const c2,  , s2),  , s2)) if c1 = c2 then inputConvSpine (valOf (modeLookup c1),  , ((s1,  , s1),  , (constType c1,  , id)),  , ((s2,  , s2),  , (constType c2,  , id))) else false inputConvSpine(mnil,  , ((s1,  , _),  , _),  , ((s2,  , _),  , _)) true inputConvSpine(mS,  , ((sClo (s1,  , s1'),  , s1),  , vs1),  , (ss2,  , vs2)) inputConvSpine (mS,  , ((s1,  , comp (s1',  , s1)),  , vs1),  , (ss2,  , vs2)) inputConvSpine(mS,  , (ss1,  , vs1),  , ((sClo (s2,  , s2'),  , s2),  , vs2)) inputConvSpine (mS,  , (ss1,  , vs1),  , ((s2,  , comp (s2',  , s2)),  , vs2)) inputConvSpine(mapp (marg (minus,  , _),  , mS),  , ((app (u1,  , s1),  , s1),  , (pi ((dec (_,  , v1),  , _),  , w1),  , t1)),  , ((app (u2,  , s2),  , s2),  , (pi ((dec (_,  , v2),  , _),  , w2),  , t2))) conv ((v1,  , t1),  , (v2,  , t2)) && inputConvSpine (mS,  , ((s1,  , s1),  , (w1,  , dot (exp (eClo (u1,  , s1)),  , t1))),  , ((s2,  , s2),  , (w2,  , dot (exp (eClo (u1,  , s1)),  , t2)))) inputConvSpine(mapp (marg (plus,  , _),  , mS),  , ((app (u1,  , s1),  , s1),  , (pi ((dec (_,  , v1),  , _),  , w1),  , t1)),  , ((app (u2,  , s2),  , s2),  , (pi ((dec (_,  , v2),  , _),  , w2),  , t2))) inputConvSpine (mS,  , ((s1,  , s1),  , (w1,  , dot (exp (eClo (u1,  , s1)),  , t1))),  , ((s2,  , s2),  , (w2,  , dot (exp (eClo (u2,  , s2)),  , t2))))(* removeDuplicates ops = ops'

       Invariant:
       If   ops is a list of recursion operators,
       then ops' is a sublist of ops, s.t.
         forall S = ((G, M), V) in ops'
               |- G ctx
               G |- M mtx
               G |- V = {V0} .. {Vn} a ; S : type
               and Vi = ci ; S'
               and forall 1 <= i <= n:
                 either ci =/= c0 orelse
                 G, V0 .. Vi |- V0 [^ i] =/=+ Vi (not convertible on + arguments on c0)
    *)
let rec removeDuplicatesnil nil removeDuplicates(s' :: ops) let let rec compExp(vs1,  , vs2) compExpW (whnf vs1,  , whnf vs2) compExpW(vs1,  , (root _,  , _)) false compExpW(vs1 as (v1,  , s1),  , (pi ((d2,  , _),  , v2),  , s2)) compDec (vs1,  , (d2,  , s2)) || compExp ((v1,  , comp (s1,  , shift)),  , (v2,  , dot1 s2)) compDec(vs1,  , (dec (_,  , v2),  , s2)) inputConv (vs1,  , (v2,  , s2))let rec check(state (name,  , gM,  , v)) checkW (whnf (v,  , id)) checkW(pi ((d,  , _),  , v),  , s) checkDec ((d,  , comp (s,  , shift)),  , (v,  , dot1 s)) checkDec((dec (_,  , v1),  , s1),  , vs2) compExp ((v1,  , s1),  , vs2) in if check s' then removeDuplicates ops else s' :: (removeDuplicates ops)(* fillOps ops = ops'

       Invariant:
       If   ops is a list of lazy recursion operators
       then ops' is a list of recursion operators combined with a filling
         operator to fill non-index variables.
    *)
let rec fillOpsnil nil fillOps(s' :: ops) let let rec fillOps'nil nil fillOps'(o :: _) (apply o)let  in in (fillOps' fillop) @ (fillOps ops)(* expandEager S = ops'

       Invariant:
       If   S State
       then ops' a list of operations which cause a recursive call
         (all variables of recursive call are instantiated)
    *)
let rec expandEagers removeDuplicates (fillOps (expandLazy s))let rec applys slet rec menu(s as state (name,  , prefix (g',  , m',  , b'),  , pi ((dec (_,  , v),  , _),  , _))) "Recursion : " ^ (expToString (g',  , v))let rec handleExceptionsfp try  with let  inlet  inlet  inlet  in(* local *)
end