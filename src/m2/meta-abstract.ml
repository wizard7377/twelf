MetaAbstract  Global GLOBAL    MetaSyn' METASYN    MetaGlobal METAGLOBAL    Abstract ABSTRACT    ModeTable MODETABLE    Whnf WHNF    Print PRINT    Constraints CONSTRAINTS    Unify UNIFY    Names NAMES    TypeCheck TYPECHECK    Subordinate SUBORDINATE     METAABSTRACT  struct module exception module module module module (* Invariants? *)
(* Definition: Mode dependency order

       A pair ((G, M), V) is in mode dependency order iff
           G |- V : type
           G |- M modes
       and G = G0+, G1-, G1+,  ... G0-
       and V = {xn:Vn} ..{x1:V1}P0
       where G0+ collects all +variables when traversing P0 in order
       and Gi+ collects all +variables when traverseing Vi in order  (i > 0)
       and Gi- collects all -variables when traversing Vi in order   (i > 0)
       and G0- collects all -variables when traversing P0 in order.
    *)
type Var(*       | BV                     *)
(*--------------------------------------------------------------------*)
(* First section: Collecting EVars and BVars in mode dependency order *)
(*--------------------------------------------------------------------*)
(* checkEmpty Cnstr = ()
       raises Error exception if constraints Cnstr cannot be simplified
       to the empty constraint
    *)
let rec checkEmpty(nil) () checkEmpty(cnstr) (match simplify cnstr with nil -> () _ -> raise (error "Unresolved constraints"))(* Let G x A: defined as

       .      x .            = .
       (G, V) x (A, BVar)    = (G x A), V
       (G, V) x (A, EVar V') = (G, V x A), V'

       Then all A : Atx satisfy the following invariant: |- A Atx

       ? If    A = A', EV (r, V, m)
       ? then  . |- V = {G x A'}.V' : type
       ? where G x A' |- V' : type

       We write A ||- U if all EVars and BVars of U are collected in A,
       A ||- S if all EVars and BVars of S are collected in A,
       and similiar notation for the other syntactic categories.
    *)
(* typecheck ((G, M), V) = ()

       Invariant:
       If G |- V : type
       then typecheck returns ()
       else TypeCheck.Error is raised
    *)
let rec typecheck(prefix (g,  , m,  , b),  , v) typeCheck (g,  , (v,  , uni type))(* modeEq (marg, st) = B'

       Invariant:
       If   (marg = + and st = top) or (marg = - and st = bot)
       then B' = true
       else B' = false
    *)
let rec modeEq(marg (plus,  , _),  , top) true modeEq(marg (minus,  , _),  , bot) true modeEq_ false(* atxLookup (atx, r)  = Eopt'

       Invariant:
       If   r exists in atx as EV (V)
       then Eopt' = SOME EV and . |- V : type
       else Eopt' = NONE
    *)
let rec atxLookup(null,  , _) nONE atxLookup(decl (m,  , bV),  , r) atxLookup (m,  , r) atxLookup(decl (m,  , e as eV (r',  , _,  , _)),  , r) if (r = r') then sOME e else atxLookup (m,  , r)(* raiseType (k, G, V) = {{G'}} V

       Invariant:
       If G |- V : L
          G = G0, G'  (so k <= |G|)
       then  G0 |- {{G'}} V : L
             |G'| = k

       All abstractions are potentially dependent.
    *)
let rec raiseType(0,  , g,  , v) v raiseType(depth,  , decl (g,  , d),  , v) raiseType (depth - 1,  , g,  , pi ((d,  , maybe),  , v))(* weaken (depth,  G, a) = (w')
    *)
let rec weaken(0,  , g,  , a) id weaken(depth,  , decl (g',  , d as dec (name,  , v)),  , a) let let  in in if belowEq (targetFam v,  , a) then dot1 w' else comp (w',  , shift)(* countPi V = n'

       If   G |- x : V
       and  V = {G'} V'
       then |G'| = n'
    *)
(* V in nf or enf? -fp *)
let rec countPiv let let rec countPi'(root _,  , n) n countPi'(pi (_,  , v),  , n) countPi' (v,  , n + 1) countPi'(eClo (v,  , _),  , n) countPi' (v,  , n) in countPi' (v,  , 0)(* collectExp (lG0, G, (U, s), mode, (A, depth)) = (A', depth')
       collects EVar's and BVar's in mode dependency order!
       depth is needed to decide if a BVar is encountered for the first time.

       Invariant:
       Let A : auxiliary context,
           depth : length of the subcontext of G, which must still
                   be traversed and collected

       If   G  |- s : G'  and   G' |- U : V
       and  G = G0, G0', GO'', Gp
       and  . |- A Atx
       and  |G0,  G0', G0''| =  lG0
       and       |G0', G0''| = depth
       then           |G0''| = depth'
       and  . |- A' Atx
       and  A' = A, A''
       and  A'' ||- U [s]
    *)
let rec collectExp(lG0,  , g,  , us,  , mode,  , adepth) collectExpW (lG0,  , g,  , whnf us,  , mode,  , adepth) collectExpW(lG0,  , g,  , (uni _,  , s),  , mode,  , adepth) adepth collectExpW(lG0,  , g,  , (pi ((d,  , _),  , v),  , s),  , mode,  , adepth) collectExp (lG0,  , decl (g,  , decSub (d,  , s)),  , (v,  , dot1 s),  , mode,  , collectDec (lG0,  , g,  , (d,  , s),  , mode,  , adepth)) collectExpW(lG0,  , g,  , (lam (d,  , u),  , s),  , mode,  , adepth) collectExp (lG0,  , decl (g,  , decSub (d,  , s)),  , (u,  , dot1 s),  , mode,  , collectDec (lG0,  , g,  , (d,  , s),  , mode,  , adepth)) collectExpW(lG0,  , g,  , us as (root (bVar (k),  , s),  , s),  , mode,  , adepth as (a,  , depth)) let let  in in if (k = l + depth - lG0) && depth > 0 then let let  in(* invariant: all variables (EV or BV) in V already seen! *)
 in collectSpine (lG0,  , g,  , (s,  , s),  , mode,  , (decl (a,  , bV),  , depth - 1)) else collectSpine (lG0,  , g,  , (s,  , s),  , mode,  , adepth) collectExpW(lG0,  , g,  , (root (c,  , s),  , s),  , mode,  , adepth) collectSpine (lG0,  , g,  , (s,  , s),  , mode,  , adepth) collectExpW(lG0,  , g,  , (eVar (r,  , gX,  , v,  , cnstrs),  , s),  , mode,  , adepth as (a,  , depth)) (match atxLookup (a,  , r) with nONE -> let let  inlet  in(* lGp' >= 0 *)
let  inlet  inlet  inlet  in(* lGp'' >= 0 *)
let  inlet  inlet  in(* invariant: all variables (EV) in Vraised already seen *)
 in collectSub (lG0,  , g,  , lGp'',  , s,  , mode,  , (decl (a,  , eV (r',  , vraised,  , mode)),  , depth)) sOME (eV (_,  , v,  , _)) -> let let  in in collectSub (lG0,  , g,  , lGp',  , s,  , mode,  , adepth)) collectExpW(lGO,  , g,  , (fgnExp csfe,  , s),  , mode,  , adepth) fold csfe (fun (u,  , adepth') -> collectExp (lGO,  , g,  , (u,  , s),  , mode,  , adepth')) adepth(* hack - should discuss with cs    -rv *)
(* collectSub (lG0, G, lG'', s, mode, (A, depth)) = (A', depth')
       collects EVar's and BVar's in mode dependency order!
       depth is needed to decide if a BVar is encountered for the first time.

       Invariant:
       Let A : auxiliary context,
           depth : length of the subcontext of G, which must still
                   be traversed and collected

       If   G  |- s : G'
       and  G = G0, G0', GO'', Gp
       and  . |- A Atx
       and  |G0,  G0', G0''| =  lG0
       and       |G0', G0''| = depth
       and  G' = GO, G''
       and  |G''| = lG''
       then           |G0''| = depth'
       and  . |- A' Atx
       and  A' = A, A''
       and  A'' ||- s   (for the first |G'| elements of s)
    *)
 collectSub(_,  , _,  , 0,  , _,  , _,  , adepth) adepth collectSub(lG0,  , g,  , lG',  , shift (k),  , mode,  , adepth) collectSub (lG0,  , g,  , lG',  , dot (idx (k + 1),  , shift (k + 1)),  , mode,  , adepth) collectSub(lG0,  , g,  , lG',  , dot (idx (k),  , s),  , mode,  , adepth as (a,  , depth)) collectSub (lG0,  , g,  , lG' - 1,  , s,  , mode,  , adepth) collectSub(lG0,  , g,  , lG',  , dot (exp (u),  , s),  , mode,  , adepth) collectSub (lG0,  , g,  , lG' - 1,  , s,  , mode,  , collectExp (lG0,  , g,  , (u,  , id),  , mode,  , adepth))(* collectSpine (lG0, G, (S, s), mode, (A, depth)) = (A', depth')
       collects EVar's and BVar's in mode dependency order!
       depth is needed to decide if a BVar is encountered for the first time.

       Invariant:
       Let A : auxiliary context,
           depth : length of the subcontext of G, which must still
                   be traversed and collected

       If   G  |- s : G'  and   G' |- S : V > V'
       and  G = G0, G0', GO'', Gp
       and  . |- A Atx
       and  |G0,  G0', G0''| =  lG0
       and       |G0', G0''| = depth
       then           |G0''| = depth'
       and  . |- A' Atx
       and  A' = A, A''
       and  A'' ||- S
    *)
 collectSpine(lG0,  , g,  , (nil,  , _),  , mode,  , adepth) adepth collectSpine(lG0,  , g,  , (sClo (s,  , s'),  , s),  , mode,  , adepth) collectSpine (lG0,  , g,  , (s,  , comp (s',  , s)),  , mode,  , adepth) collectSpine(lG0,  , g,  , (app (u,  , s),  , s),  , mode,  , adepth) collectSpine (lG0,  , g,  , (s,  , s),  , mode,  , collectExp (lG0,  , g,  , (u,  , s),  , mode,  , adepth))(* collectDec (lG0, G, (x:D, s), mode, (A, depth)) = (A', depth')
       collects EVar's and BVar's in mode dependency order!
       depth is needed to decide if a BVar is encountered for the first time.

       Invariant:
       Let A : auxiliary context,
           depth : length of the subcontext of G, which must still
                   be traversed and collected

       If   G  |- s : G'  and   G' |- D : L
       and  G = G0, G0', GO'', Gp
       and  . |- A Atx
       and  |G0,  G0', G0''| =  lG0
       and       |G0', G0''| = depth
       then           |G0''| = depth'
       and  . |- A' Atx
       and  A' = A, A''
       and  A'' ||- x:D[s]
    *)
 collectDec(lG0,  , g,  , (dec (x,  , v),  , s),  , mode,  , adepth) collectExp (lG0,  , g,  , (v,  , s),  , mode,  , adepth)(* collectModeW (lG0, G, modeIn, modeRec, (V, s) (A, depth)) = (A', depth')
       collects EVar's and BVar's in mode dependency order!
       depth is needed to decide if a BVar is encountered for the first time.

       Invariant:
       Let A : auxiliary context,
           depth : length of the subcontext of G, which must still
                   be traversed and collected

       If   G  |- s : G'  and   G' |- V : L        V[s] in whnf
       and  G = G0, G0', GO'', Gp
       and  . |- A Atx
       and  |G0,  G0', G0''| =  lG0
       and       |G0', G0''| = depth
       then           |G0''| = depth'
       and  . |- A' Atx
       and  A' = A, A''
       and  A'' ||- V
       and  A'' consists of all EVars/BVars marked with modeIn in V and
                recored as modeRec
    *)
let rec collectModeW(lG0,  , g,  , modeIn,  , modeRec,  , (root (const cid,  , s),  , s),  , adepth) let let rec collectModeW'(((nil,  , _),  , mnil),  , adepth) adepth collectModeW'(((sClo (s,  , s'),  , s),  , m),  , adepth) collectModeW' (((s,  , comp (s',  , s)),  , m),  , adepth) collectModeW'(((app (u,  , s),  , s),  , mapp (m,  , mS)),  , adepth) collectModeW' (((s,  , s),  , mS),  , if modeEq (m,  , modeIn) then collectExp (lG0,  , g,  , (u,  , s),  , modeRec,  , adepth) else adepth)let  in in collectModeW' (((s,  , s),  , mS),  , adepth) collectModeW(lG0,  , g,  , modeIn,  , modeRec,  , (pi ((d,  , p),  , v),  , s),  , adepth) raise (error ("Implementation restricted to the Horn fragment of the meta logic"))(* collectG (lG0, G, (V, s) (A, depth)) = (A', depth')
       collects EVar's and BVar's in mode dependency order!
       depth is needed to decide if a BVar is encountered for the first time.

       Invariant:
       Let A : auxiliary context,
           depth : length of the subcontext of G, which must still
                   be traversed and collected

       If   G  |- s : G'  and   G' |- V : L
       and  G = G0, G0', GO'', Gp
       and  . |- A Atx
       and  |G0,  G0', G0''| =  lG0
       and       |G0', G0''| = depth
       then           |G0''| = depth'
       and  . |- A' Atx
       and  A' = A, A''
       and  A'' ||- V
       and  A'' consists of all Top EVars/BVars in the head of V
                    followed by Bot/Top EVars/BVars of recursive calls
                    (A'' is in mode dependecy order)
    *)
let rec collectG(lG0,  , g,  , vs,  , adepth) collectGW (lG0,  , g,  , whnf vs,  , adepth) collectGW(lG0,  , g,  , vs,  , adepth) collectModeW (lG0,  , g,  , bot,  , top,  , vs,  , collectModeW (lG0,  , g,  , top,  , bot,  , vs,  , adepth))(* collectDTop (lG0, G, (V, s) (A, depth)) = (A', depth')
       collects EVar's and BVar's in mode dependency order!
       depth is needed to decide if a BVar is encountered for the first time.

       Invariant:
       Let A : auxiliary context,
           depth : length of the subcontext of G, which must still
                   be traversed and collected

       If   G  |- s : G'  and   G' |- V : L
       and  G = G0, G0', GO'', Gp
       and  . |- A Atx
       and  |G0,  G0', G0''| =  lG0
       and       |G0', G0''| = depth
       then           |G0''| = depth'
       and  . |- A' Atx
       and  A' = A, A''
       and  A'' ||- V
       and  A'' consists of all Top EVars/BVars in the head of V
                    followed by Bot/Top EVars/BVars of recursive calls
                    (A'' is in mode dependecy order)
    *)
let rec collectDTop(lG0,  , g,  , vs,  , adepth) collectDTopW (lG0,  , g,  , whnf vs,  , adepth) collectDTopW(lG0,  , g,  , (pi ((d as dec (x,  , v1),  , no),  , v2),  , s),  , adepth) collectG (lG0,  , g,  , (v1,  , s),  , collectDTop (lG0,  , decl (g,  , decSub (d,  , s)),  , (v2,  , dot1 s),  , adepth)) collectDTopW(lG0,  , g,  , vs as (root _,  , s),  , adepth) collectModeW (lG0,  , g,  , top,  , top,  , vs,  , adepth)(* collectDBot (lG0, G, (V, s), (A, depth)) = (A', depth')
       collects EVar's and BVar's in mode dependency order!
       depth is needed to decide if a BVar is encountered for the first time.

       Invariant:
       Let A : auxiliary context,
           depth : length of the subcontext of G, which must still
                   be traversed and collected

       If   G  |- s : G'  and   G' |- V : L
       and  G = G0, G0', GO'', Gp
       and  . |- A Atx
       and  |G0,  G0', G0''| =  lG0
       and       |G0', G0''| = depth
       then           |G0''| = depth'
       and  . |- A' Atx
       and  A' = A, A''
       and  A'' ||- V
       and  A'' consists of all Top EVars/BVars in the head of V
                    followed by Bot/Top EVars/BVars of recursive calls
                    followed by Top EVars/BVars in the head of V
                    (A'' is in mode dependecy order)
    *)
let rec collectDBot(lG0,  , g,  , vs,  , adepth) collectDBotW (lG0,  , g,  , whnf vs,  , adepth) collectDBotW(lG0,  , g,  , (pi ((d,  , _),  , v),  , s),  , adepth) collectDBot (lG0,  , decl (g,  , decSub (d,  , s)),  , (v,  , dot1 s),  , adepth) collectDBotW(lG0,  , g,  , vs as (root _,  , s),  , adepth) collectModeW (lG0,  , g,  , bot,  , bot,  , vs,  , adepth)(* collect ((G,_,_), V) = A'
       collects EVar's and BVar's in V mode dependency order.

       Invariant:
       If   G  |- s : G'  and   G' |- V : L
       then . |- A' Atx
       and  A' = A, A''
       and  A'' ||- V
       and  A'' consists of all Top EVars/BVars in the head of V
                    followed by Bot/Top EVars/BVars of recursive calls
                    followed by Top EVars/BVars in the head of V
                    (A'' is in mode dependecy order)
    *)
let rec collect(prefix (g,  , m,  , b),  , v) let let  inlet  in in a(*------------------------------------------------------------*)
(* Second section: Abstracting over EVars and BVars that have *)
(* been collected in mode dependency order                    *)
(*------------------------------------------------------------*)
(* lookupEV (A, r) = (k', V')

       Invariant:

       If   A ||- V
       and  G |- X : V' occuring in V
       then G x A |- k : V'
       and  . |- V' : type
    *)
let rec lookupEV(a,  , r) let let rec lookupEV'(decl (a,  , eV (r,  , v,  , _)),  , r',  , k) if (r = r') then (k,  , v) else lookupEV' (a,  , r',  , k + 1) lookupEV'(decl (a,  , bV),  , r',  , k) lookupEV' (a,  , r',  , k + 1)(* lookupEV' I.Null cannot occur by invariant *)
 in lookupEV' (a,  , r,  , 1)(* lookupBV (A, i) = k'

       Invariant:

       If   A ||- V
       and  G |- V type
       and  G [x] A |- i : V'
       then ex a substititution  G x A |- s : G [x] A
       and  G x A |- k' : V''
       and  G x A |- V' [s] = V'' : type
    *)
let rec lookupBV(a,  , i) let let rec lookupBV'(decl (a,  , eV (r,  , v,  , _)),  , i,  , k) lookupBV' (a,  , i,  , k + 1) lookupBV'(decl (a,  , bV),  , 1,  , k) k lookupBV'(decl (a,  , bV),  , i,  , k) lookupBV' (a,  , i - 1,  , k + 1)(* lookupBV' I.Null cannot occur by invariant *)
 in lookupBV' (a,  , i,  , 1)(* abstractExpW (A, G, depth, (U, s)) = U'

       Invariant:
       If    G0, G |- s : G1   G1 |- U : V    (U,s) in whnf
       and   |G| = depth
       and   A is auxiliary context in mode dependency order
       and   A ||- U  and  A ||- V
       then  G0 x A, G |- U' : V'
       and   . ||- U' and . ||- V'
       and   U' is in nf
    *)
let rec abstractExpW(a,  , g,  , depth,  , (v as uni (l),  , s)) v abstractExpW(a,  , g,  , depth,  , (pi ((d,  , p),  , v),  , s)) piDepend ((abstractDec (a,  , g,  , depth,  , (d,  , s)),  , p),  , abstractExp (a,  , decl (g,  , decSub (d,  , s)),  , depth + 1,  , (v,  , dot1 s))) abstractExpW(a,  , g,  , depth,  , (lam (d,  , u),  , s)) lam (abstractDec (a,  , g,  , depth,  , (d,  , s)),  , abstractExp (a,  , decl (g,  , decSub (d,  , s)),  , depth + 1,  , (u,  , dot1 s))) abstractExpW(a,  , g,  , depth,  , (root (c as bVar k,  , s),  , s)) if k > depth then let let  in in root (bVar (k' + depth),  , abstractSpine (a,  , g,  , depth,  , (s,  , s))) else root (c,  , abstractSpine (a,  , g,  , depth,  , (s,  , s))) abstractExpW(a,  , g,  , depth,  , (root (c,  , s),  , s)) root (c,  , abstractSpine (a,  , g,  , depth,  , (s,  , s))) abstractExpW(a,  , g,  , depth,  , (eVar (r,  , _,  , v,  , _),  , s)) let let  in(* IMPROVE: remove the raised variable, replace by V -cs ?-fp *)
 in root (bVar (k + depth),  , abstractSub (a,  , g,  , depth,  , (vraised,  , id),  , s,  , targetFam v,  , nil)) abstractExpW(a,  , g,  , depth,  , (fgnExp csfe,  , s)) apply csfe (fun u -> abstractExp (a,  , g,  , depth,  , (u,  , s)))(* hack - should discuss with cs     -rv *)
(* abstractExp, same as abstractExpW, but (V, s) need not be in whnf *)
 abstractExp(a,  , g,  , depth,  , us) abstractExpW (a,  , g,  , depth,  , whnf us)(* abstractSpine (A, G, depth, (S, s)) = U'

       Invariant:
       If    G0, G |- s : G1   G1 |- S : V1 > V2
       and   |G| = depth
       and   A is auxiliary context in mode dependency order
       and   A ||- U  and  H ||- V1
       then  G0 x A, G |- S' : V1' > V2'
       and   . ||- S' and . ||- V1'
    *)
 abstractSpine(a,  , g,  , depth,  , (nil,  , _)) nil abstractSpine(a,  , g,  , depth,  , (app (u,  , s),  , s)) app (abstractExp (a,  , g,  , depth,  , (u,  , s)),  , abstractSpine (a,  , g,  , depth,  , (s,  , s))) abstractSpine(a,  , g,  , depth,  , (sClo (s,  , s'),  , s)) abstractSpine (a,  , g,  , depth,  , (s,  , comp (s',  , s)))(* abstractSub (A, G, depth, (XV, t), s, b, S) = S'

       Invariant:
       If    G0, G |- s : G'
       and   |G| = depth
       and   A is auxiliary context in mode dependency order
       and   A ||- s
       then  G0 x A, G |- S' : {XV [t]}.W > W
       and   . ||- S'
    *)
(* optimize: whnf not necessary *)
 abstractSub(a,  , g,  , depth,  , xVt,  , s,  , b,  , s) abstractSubW (a,  , g,  , depth,  , whnf xVt,  , s,  , b,  , s) abstractSubW(a,  , g,  , depth,  , (root _,  , _),  , s,  , b,  , s) s abstractSubW(a,  , g,  , depth,  , xVt as (pi _,  , _),  , shift k,  , b,  , s) abstractSub (a,  , g,  , depth,  , xVt,  , dot (idx (k + 1),  , shift (k + 1)),  , b,  , s) abstractSubW(a,  , g,  , depth,  , xVt as (pi (_,  , xV'),  , t),  , dot (idx (k),  , s),  , b,  , s) let let  in in if k > depth then let let  in in abstractSub (a,  , g,  , depth,  , (xV',  , dot1 t),  , s,  , b,  , app (root (bVar (k' + depth),  , nil),  , s)) else abstractSub (a,  , g,  , depth,  , (xV',  , dot1 t),  , s,  , b,  , app (root (bVar (k),  , nil),  , s)) abstractSubW(a,  , g,  , depth,  , xVt as (pi (_,  , xV'),  , t),  , dot (exp (u),  , s),  , b,  , s) abstractSub (a,  , g,  , depth,  , (xV',  , dot1 t),  , s,  , b,  , app (abstractExp (a,  , g,  , depth,  , (u,  , id)),  , s))(* abstractDec (A, G, depth, (x:V, s)) = x:V'

       Invariant:
       If    G0, G |- s : G1   G1 |- V : L
       and   |G| = G
       and   |G| = depth
       and   A is auxiliary context in mode dependency order
       and   A ||- V
       then  G0 x A, G |- V' : L
       and   . ||- V'
    *)
 abstractDec(a,  , g,  , depth,  , (dec (xOpt,  , v),  , s)) dec (xOpt,  , abstractExp (a,  , g,  , depth,  , (v,  , s)))(* abstractCtx (A, (G, M)) = ((G', M') , G'')

       Let E be a list of EVars possibly occuring in G

       Invariant:
       G' = G x A
       M' = M x A    (similar to G x A, but just represents mode information)
       G'' = G [x] A
    *)
let rec abstractCtx(null,  , gM as prefix (null,  , null,  , null)) (gM,  , null) abstractCtx(decl (a,  , bV),  , prefix (decl (g,  , d),  , decl (m,  , marg),  , decl (b,  , b))) let let  inlet  inlet  inlet  in in (prefix (decl (g',  , decName (g',  , d')),  , decl (m',  , marg),  , decl (b',  , b)),  , decl (lG',  , d')) abstractCtx(decl (a,  , eV (r,  , v,  , m)),  , gM) let let  inlet  inlet  in in (prefix (decl (g',  , decName (g',  , dec (nONE,  , v''))),  , decl (m',  , m),  , decl (b',  , match m with top -> ! maxSplit bot -> 0)),  , lG')(* abstract ((G, M), V) = ((G', M') , V')

       Invariant:
       If    G |- V : type    (M modes associated with G)
       then  G' |- V' : type  (M' modes associated with G')
       and   . ||- V'
    *)
let rec abstract(s as state (name,  , gM as prefix (g,  , m,  , b),  , v)) let let  inlet  inlet  inlet  inlet  inlet  in in slet  in(* local *)
end