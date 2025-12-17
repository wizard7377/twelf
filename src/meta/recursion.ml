MTPRecursion  MTPGlobal MTPGLOBAL    Global GLOBAL    StateSyn' STATESYN    Abstract ABSTRACT    MTPAbstract MTPABSTRACT    MTPAbstract StateSyn  StateSyn'   FunTypeCheck FUNTYPECHECK    FunTypeCheck StateSyn  StateSyn'   MTPrint MTPRINT    MTPrint StateSyn  StateSyn'   Whnf WHNF    Unify UNIFY    Conv CONV    Names NAMES    Subordinate SUBORDINATE    Print PRINT    TypeCheck TYPECHECK    Formatter FORMATTER    FunPrint FUNPRINT    FunPrint Formatter  Formatter    MTPRECURSION  struct module exception type Operatormodule module module module module module type Dec(* Residual Lemma *)
let rec closedCtx(null) () closedCtx(decl (g,  , d)) if closedDec (g,  , (d,  , id)) then raise (domain) else closedCtx g(*  spine n = S'

        Invariant:
        S' = n;..;1;Nil
     *)
let rec spine0 nil spinen app (root (bVar n,  , nil),  , spine (n - 1))(* someEVars (G, G1, s) = s'

       Invariant:
       If  |- G ctx
       and  G |- s : G
       then G |- s' : G, G1
    *)
let rec someEVars(g,  , nil,  , s) s someEVars(g,  , dec (_,  , v) :: l,  , s) someEVars (g,  , l,  , dot (exp (newEVar (g,  , eClo (v,  , s))),  , s))(* ctxSub (G, s) = G'

       Invariant:
       If   G2 |- s : G1
       and  G1 |- G ctx
       then G2 |- G' = G[s] ctx

       NOTE, should go into a different module. Code duplication!
    *)
let rec ctxSub(nil,  , s) nil ctxSub(d :: g,  , s) decSub (d,  , s) :: ctxSub (g,  , dot1 s)(* appendCtx ((G1, B1), T, G2) = (G', B')

       Invariant:
       If   |- G1 ctx
       and  G1 |- B1 tags
       and  T tag
       and  G1 |- G2 ctx
       then |- G' = G1, G2 ctx
       and  G' |- B' tags
    *)
let rec appendCtx(gB1,  , t,  , nil) gB1 appendCtx((g1,  , b1),  , t,  , d :: g2) appendCtx ((decl (g1,  , d),  , decl (b1,  , t)),  , t,  , g2)(* createCtx ((G, B), ll, s) = ((G', B'), s', af')

     Invariant:
     If   |- G ctx
     and  G |- B tags
     and  . |- label list
     and  |- G1 ctx
     and  G |- s : G1

     then |- G' : ctx
     and  G' |- B' tags
     and  G' = G, G''
     and  G' |- s' : G1
     and  af : forall . |- AF aux formulas. Ex . |- AF' = {{G''}} AF  auxFor
     *)
let rec createCtx((g,  , b),  , nil,  , s) ((g,  , b),  , s,  , fun aF -> aF) createCtx((g,  , b),  , n :: ll,  , s) let let  inlet  in(* G |- s' : G1 *)
let  in(* G |- G2' ctx *)
let  in(* . |- G' = G, G2' ctx *)
let  in(* G' |- s'' : G0 *)
let  in in (gB'',  , s'',  , fun aF -> block ((g,  , t,  , length g1,  , g2'),  , af'' aF))(* createEVars' (G, G0) = s'

       Invariant :
       If   |- G ctx
       and  |- G0 ctx
       then G |- s' : G0
       and  s' = X1 .. Xn where n = |G0|
    *)
let rec createEVars(g,  , null) shift (ctxLength g) createEVars(g,  , decl (g0,  , dec (_,  , v))) let let  in in dot (exp (newEVar (g,  , eClo (v,  , s))),  , s)(* checkCtx (G, G2, (V, s)) = B'

       Invariant:
       If   |- G = G0, G1 ctx
       and  G |- G2 ctx
       and  G |- s : G0
       and  G0 |- V : L
       then B' holds iff
            G1 = V1 .. Vn and G, G1, V1 .. Vi-1 |- Vi unifies with V [s o ^i] : L
    *)
let rec checkCtx(g,  , nil,  , (v2,  , s)) false checkCtx(g,  , (d as dec (_,  , v1)) :: g2,  , (v2,  , s)) (trail (fun () -> unifiable (g,  , (v1,  , id),  , (v2,  , s))) || checkCtx (decl (g,  , d),  , g2,  , (v2,  , comp (s,  , shift))))(* checkLabels ((G', B'), V, ll, l) = lopt'

       Invariant:
       If   |- G' ctx
       and  G' |- B' ctx
       and  G' |- s : G0
       and  G0 |- V : type
       and  . |- ll label list
       and  . |- l label number
       then lopt' = NONE if no context block is applicable
       or   lopt' = SOME l' if context block l' is applicable

       NOTE: For this implementation we only pick the first applicable contextblock.
       It is not yet clear what should happen if there are inductive calls where more
       then one contextblocks are introduced --cs
    *)
let rec checkLabels((g',  , b'),  , (v,  , s),  , ll, (* as nil *)
,  , l) if l < 0 then nONE else let let  inlet  inlet  inlet  in(* G' |- t : G1 *)
let  in(* G |- G2' ctx *)
 in if not (exists (fun l' -> l = l') ll) && checkCtx (g',  , g2',  , (v,  , s)) then sOME l else checkLabels ((g',  , b'),  , (v,  , s),  , ll,  , l - 1)(*      | checkLabels _ = NONE  (* more than one context block is introduced *) *)
(* appendRL (Ds1, Ds2) = Ds'

       Invariant:
       Ds1, Ds2 are a list of residual lemmas
       Ds' = Ds1 @ Ds2, where all duplicates are removed
    *)
let rec appendRL(nil,  , ds) ds appendRL((l as lemma (n,  , f)) :: ds1,  , ds2) let let  in in if exists (fun (lemma (n',  , f')) -> (n = n') && convFor ((f,  , id),  , (f',  , id))) ds' then ds' else l :: ds'(* recursion ((nih, Gall, Fex, Oex), (ncurrent, (G0, B0), ll, Ocurrent, H, F)) = Ds

       Invariant:

       If

       nih  is the id or the induction hypothesis
       |- Gall ctx
       Gall |- Fex : for        (Fex doesn't contain any universal quantifiers)
       Gall |- Oex : order

       and
       ncurrent is the id of the current proof goal
       |- G0 ctx
       G0 |- B0 tags
       . |- ll label list
       G0 |- Ocurrent order
       G0 |- H history
       G0 |- F formula

       then
       G0 |- Ds decs
    *)
let rec recursion((nih,  , gall,  , fex,  , oex),  , (ncurrent,  , (g0,  , b0),  , ll,  , ocurrent,  , h,  , f)) let let  in(* G' |- s' : G0 *)
let  in(* G' |- t' : Gall *)
let  inlet  inlet  inlet rec scds let let  in in if exists (fun (nhist,  , fhist) -> nih = nhist && convFor ((fnew,  , id),  , (fhist,  , id))) h then ds else lemma (nih,  , fnew) :: dslet rec ac((g',  , b'),  , vs,  , ds) (match checkLabels ((g',  , b'),  , vs,  , ll,  , labelSize () - 1) with nONE -> ds sOME l' -> let let  in in appendRL (ds',  , ds)) in if ncurrent < nih then ordle ((g',  , b'),  , oex',  , ocurrent',  , sc,  , ac,  , nil) else ordlt ((g',  , b'),  , oex',  , ocurrent',  , sc,  , ac,  , nil)(* set_parameter (GB, X, k, sc, ac, S) = S'

       Invariant:
       appends a list of recursion operators to S after
       instantiating X with all possible local parameters (between 1 and k)
    *)
 set_parameter(gB as (g1,  , b1),  , x as eVar (r,  , _,  , v,  , _),  , k,  , sc,  , ac,  , ds) let (* set_parameter' ((G, B), k, Ds) = Ds'

           Invariant:
           If    G1, D < G
        *)
let rec set_parameter'((null,  , null),  , _,  , ds) ds set_parameter'((decl (g,  , d),  , decl (b,  , parameter _)),  , k,  , ds) let let  inlet  in in set_parameter' ((g,  , b),  , k + 1,  , ds') set_parameter'((decl (g,  , d),  , decl (b,  , _)),  , k,  , ds) set_parameter' ((g,  , b),  , k + 1,  , ds) in set_parameter' (gB,  , 1,  , ds)(* ltinit (GB, k, ((U1, s1), (V2, s2)), ((U3, s3), (V4, s4)), sc, ac, Ds) = Ds'

       Invariant:
       If   G = G0, Gp    (G0, global context, Gp, parameter context)
       and  |Gp| = k
       and  G |- s1 : G1   G1 |- U1 : V1
       and  G |- s2 : G2   G2 |- V2 : L
                G |- s3 : G1   G1 |- U3 : V3
       and  G |- s4 : G2   G2 |- V4 : L
       and  G |- V1[s1] == V2 [s2]
       and  G |- V3[s3] == V4 [s5]
       and  Ds is a set of all all possible states
       and  sc is success continuation
       then Ds' is an extension of Ds, containing all
            recursion operators
    *)
 ltinit(gB,  , k,  , (us,  , vs),  , usVs',  , sc,  , ac,  , ds) ltinitW (gB,  , k,  , whnfEta (us,  , vs),  , usVs',  , sc,  , ac,  , ds) ltinitW(gB,  , k,  , (us,  , vs as (root _,  , _)),  , usVs',  , sc,  , ac,  , ds) lt (gB,  , k,  , (us,  , vs),  , usVs',  , sc,  , ac,  , ds) ltinitW((g,  , b),  , k,  , ((lam (d1,  , u),  , s1),  , (pi (d2,  , v),  , s2)),  , ((u',  , s1'),  , (v',  , s2')),  , sc,  , ac,  , ds) ltinit ((decl (g,  , decSub (d1,  , s1), (* = I.decSub (D2, s2) *)
),  , decl (b,  , parameter nONE)),  , k + 1,  , ((u,  , dot1 s1),  , (v,  , dot1 s2)),  , ((u',  , comp (s1',  , shift)),  , (v',  , comp (s2',  , shift))),  , sc,  , ac,  , ds)(* lt (GB, k, ((U, s1), (V, s2)), (U', s'), sc, ac, Ds) = Ds'

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
       and  Ds is a set of already calculuate possible states
       and  sc is success continuation
           then Ds' is an extension of Ds, containing all
                recursion operators
    *)
(* Vs is Root!!! *)
(* (Us',Vs') may not be eta-expanded!!! *)
 lt(gB,  , k,  , (us,  , vs),  , (us',  , vs'),  , sc,  , ac,  , ds) ltW (gB,  , k,  , (us,  , vs),  , whnfEta (us',  , vs'),  , sc,  , ac,  , ds) ltW(gB,  , k,  , (us,  , vs),  , ((root (const c,  , s'),  , s'),  , vs'),  , sc,  , ac,  , ds) ltSpine (gB,  , k,  , (us,  , vs),  , ((s',  , s'),  , (constType c,  , id)),  , sc,  , ac,  , ds) ltW(gB as (g,  , b),  , k,  , (us,  , vs),  , ((root (bVar n,  , s'),  , s'),  , vs'),  , sc,  , ac,  , ds) (match ctxLookup (b,  , n) with parameter _ -> let let  in in ltSpine (gB,  , k,  , (us,  , vs),  , ((s',  , s'),  , (v',  , id)),  , sc,  , ac,  , ds) lemma _ -> ds) ltW(gB,  , _,  , _,  , ((eVar _,  , _),  , _),  , _,  , _,  , ds) ds ltW(gB as (g,  , b),  , k,  , ((u,  , s1),  , (v,  , s2)),  , ((lam (d as dec (_,  , v1'),  , u'),  , s1'),  , (pi ((dec (_,  , v2'),  , _),  , v'),  , s2')),  , sc,  , ac,  , ds) let let  in(* ctxBlock (GB, I.EClo (V1', s1'), k, sc, ac, Ds) *)
 in if equiv (targetFam v,  , targetFam v1')(* == I.targetFam V2' *)
 then let (* enforce that X gets only bound to parameters *)
let  in(* = I.newEVar (I.EClo (V2', s2')) *)
let  in in lt (gB,  , k,  , ((u,  , s1),  , (v,  , s2)),  , ((u',  , dot (exp (x),  , s1')),  , (v',  , dot (exp (x),  , s2'))),  , sc',  , ac,  , ds') else if below (targetFam v1',  , targetFam v) then let let  in(* = I.newEVar (I.EClo (V2', s2')) *)
 in lt (gB,  , k,  , ((u,  , s1),  , (v,  , s2)),  , ((u',  , dot (exp (x),  , s1')),  , (v',  , dot (exp (x),  , s2'))),  , sc,  , ac,  , ds') else ds' ltSpine(gB,  , k,  , (us,  , vs),  , (ss',  , vs'),  , sc,  , ac,  , ds) ltSpineW (gB,  , k,  , (us,  , vs),  , (ss',  , whnf vs'),  , sc,  , ac,  , ds) ltSpineW(gB,  , k,  , (us,  , vs),  , ((nil,  , _),  , _),  , _,  , _,  , ds) ds ltSpineW(gB,  , k,  , (us,  , vs),  , ((sClo (s,  , s'),  , s''),  , vs'),  , sc,  , ac,  , ds) ltSpineW (gB,  , k,  , (us,  , vs),  , ((s,  , comp (s',  , s'')),  , vs'),  , sc,  , ac,  , ds) ltSpineW(gB,  , k,  , (us,  , vs),  , ((app (u',  , s'),  , s1'),  , (pi ((dec (_,  , v1'),  , _),  , v2'),  , s2')),  , sc,  , ac,  , ds) let let  in in ltSpine (gB,  , k,  , (us,  , vs),  , ((s',  , s1'),  , (v2',  , dot (exp (eClo (u',  , s1')),  , s2'))),  , sc,  , ac,  , ds')(* eq (GB, ((U, s1), (V, s2)), (U', s'), sc, ac, Ds) = Ds'

       Invariant:
       If   G |- s1 : G1   G1 |- U1 : V1   (U1 [s1] in  whnf)
       and  G |- s2 : G2   G2 |- V2 : L    (V2 [s2] in  whnf)
            G |- s3 : G1   G1 |- U3 : V3
       and  G |- s4 : G2   G2 |- V4 : L
       and  G |- V1[s1] == V2 [s2]
       and  G |- V3[s3] == V4 [s5]
       and  Ds is a set of already calculuated possible states
       and  sc is success continuation
       then Ds' is an extension of Ds, containing all
            recursion operators resulting from U[s1] = U'[s']
    *)
 eq((g,  , b),  , (us,  , vs),  , (us',  , vs'),  , sc,  , ac,  , ds) (trail (fun () -> if unifiable (g,  , vs,  , vs') && unifiable (g,  , us,  , us') then sc ds else ds))(* le (G, k, ((U, s1), (V, s2)), (U', s'), sc, ac, Ds) = Ds'

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
       and  Ds is a set of already calculuated possible states
       and  sc is success continuation
       then Ds' is an extension of Ds, containing all
            recursion operators resulting from U[s1] <= U'[s']
    *)
 le(gB,  , k,  , (us,  , vs),  , (us',  , vs'),  , sc,  , ac,  , ds) let let  in in leW (gB,  , k,  , (us,  , vs),  , whnfEta (us',  , vs'),  , sc,  , ac,  , ds') leW(gB as (g,  , b),  , k,  , ((u,  , s1),  , (v,  , s2)),  , ((lam (d as dec (_,  , v1'),  , u'),  , s1'),  , (pi ((dec (_,  , v2'),  , _),  , v'),  , s2')),  , sc,  , ac,  , ds) let let  in in if equiv (targetFam v,  , targetFam v1')(* == I.targetFam V2' *)
 then let let  in(* = I.newEVar (I.EClo (V2', s2')) *)
let  in(* enforces that X can only bound to parameter *)
 in le (gB,  , k,  , ((u,  , s1),  , (v,  , s2)),  , ((u',  , dot (exp (x),  , s1')),  , (v',  , dot (exp (x),  , s2'))),  , sc',  , ac,  , ds') else if below (targetFam v1',  , targetFam v) then let let  in(* = I.newEVar (I.EClo (V2', s2')) *)
let  inlet  in(*              val sc'' = fn Ds'' => set_parameter (GB, X, k, sc, ac, Ds'')   (* BUG -cs *)
                val Ds''' =  le (GB, k, ((U, s1), (V, s2)),
                                 ((U', I.Dot (I.Exp (X), s1')),
                                  (V', I.Dot (I.Exp (X), s2'))), sc'', ac, Ds'') *)
 in ds'' else ds' leW(gB,  , k,  , (us,  , vs),  , (us',  , vs'),  , sc,  , ac,  , ds) lt (gB,  , k,  , (us,  , vs),  , (us',  , vs'),  , sc,  , ac,  , ds)(* ordlt (GB, O1, O2, sc, ac, Ds) = Ds'

       Invariant:
       If   G |- O1 augmented subterms
       and  G |- O2 augmented subterms
       and  Ds is a set of already calculuated possible states
       and  sc is success continuation
       then Ds' is an extension of Ds, containing all
            recursion operators of all instantiations of EVars s.t. O1 is
            lexicographically smaller than O2
    *)
 ordlt(gB,  , arg usVs,  , arg usVs',  , sc,  , ac,  , ds) ltinit (gB,  , 0,  , usVs,  , usVs',  , sc,  , ac,  , ds) ordlt(gB,  , lex l,  , lex l',  , sc,  , ac,  , ds) ordltLex (gB,  , l,  , l',  , sc,  , ac,  , ds) ordlt(gB,  , simul l,  , simul l',  , sc,  , ac,  , ds) ordltSimul (gB,  , l,  , l',  , sc,  , ac,  , ds)(* ordltLex (GB, L1, L2, sc, ac, Ds) = Ds'

       Invariant:
       If   G |- L1 list of augmented subterms
       and  G |- L2 list of augmented subterms
       and  Ds is a set of already calculuated possible states
       and  sc is success continuation
       then Ds' is an extension of Ds, containing all
            recursion operators of all instantiations of EVars s.t. L1 is
            lexicographically less then L2
    *)
 ordltLex(gB,  , nil,  , nil,  , sc,  , ac,  , ds) ds ordltLex(gB,  , o :: l,  , o' :: l',  , sc,  , ac,  , ds) let let  in in ordeq (gB,  , o,  , o',  , fun ds'' -> ordltLex (gB,  , l,  , l',  , sc,  , ac,  , ds''),  , ac,  , ds')(* ordltSimul (GB, L1, L2, sc, ac, Ds) = Ds'

       Invariant:
       If   G |- L1 list of augmented subterms
       and  G |- L2 list of augmented subterms
       and  Ds is a set of already calculuated possible states
       and  sc is success continuation
       then Ds' is an extension of Ds, containing all
            recursion operators of all instantiations of EVars s.t. L1 is
            simultaneously smaller than L2
    *)
 ordltSimul(gB,  , nil,  , nil,  , sc,  , ac,  , ds) ds ordltSimul(gB,  , o :: l,  , o' :: l',  , sc,  , ac,  , ds) let let  in in ordeq (gB,  , o,  , o',  , fun ds' -> ordltSimul (gB,  , l,  , l',  , sc,  , ac,  , ds'),  , ac,  , ds'')(* ordleSimul (GB, L1, L2, sc, ac, Ds) = Ds'

       Invariant:
       If   G |- L1 list of augmented subterms
       and  G |- L2 list of augmented subterms
       and  Ds is a set of already calculuated possible states
       and  sc is success continuation
       then Ds' is an extension of Ds, containing all
            recursion operators of all instantiations of EVars s.t. L1 is
            simultaneously smaller than or equal to L2
    *)
 ordleSimul(gB,  , nil,  , nil,  , sc,  , ac,  , ds) sc ds ordleSimul(gB,  , o :: l,  , o' :: l',  , sc,  , ac,  , ds) ordle (gB,  , o,  , o',  , fun ds' -> ordleSimul (gB,  , l,  , l',  , sc,  , ac,  , ds'),  , ac,  , ds)(* ordeq (GB, O1, O2, sc, ac, Ds) = Ds'

       Invariant:
       If   G |- O1 augmented subterms
       and  G |- O2 augmented subterms
       and  Ds is a set of already calculuated possible states
       and  sc is success continuation
       then Ds' is an extension of Ds, containing all
            recursion operators of all instantiations of EVars s.t. O1 is
            convertible to O2
    *)
 ordeq((g,  , b),  , arg (us,  , vs),  , arg (us',  , vs'),  , sc,  , ac,  , ds) if unifiable (g,  , vs,  , vs') && unifiable (g,  , us,  , us') then sc ds else ds ordeq(gB,  , lex l,  , lex l',  , sc,  , ac,  , ds) ordeqs (gB,  , l,  , l',  , sc,  , ac,  , ds) ordeq(gB,  , simul l,  , simul l',  , sc,  , ac,  , ds) ordeqs (gB,  , l,  , l',  , sc,  , ac,  , ds)(* ordlteqs (GB, L1, L2, sc, ac, Ds) = Ds'

       Invariant:
       If   G |- L1 list of augmented subterms
       and  G |- L2 list of augmented subterms
       and  Ds is a set of already calculuated possible states
       and  sc is success continuation
       then Ds' is an extension of Ds, containing all
            recursion operators of all instantiations of EVars s.t. L1 is
            convertible to L2
    *)
 ordeqs(gB,  , nil,  , nil,  , sc,  , ac,  , ds) sc ds ordeqs(gB,  , o :: l,  , o' :: l',  , sc,  , ac,  , ds) ordeq (gB,  , o,  , o',  , fun ds' -> ordeqs (gB,  , l,  , l',  , sc,  , ac,  , ds'),  , ac,  , ds)(* ordeq (GB, O1, O2, sc, ac, Ds) = Ds'

       Invariant:
       If   G |- O1 augmented subterms
       and  G |- O2 augmented subterms
       and  Ds is a set of already calculuated possible states
       and  sc is success continuation
       then Ds' is an extension of Ds, containing all
            recursion operators of all instantiations of EVars s.t. O1 is
            convertible to O2 or smaller than O2
    *)
 ordle(gB,  , o,  , o',  , sc,  , ac,  , ds) let let  in in ordlt (gB,  , o,  , o',  , sc,  , ac,  , ds')(* skolem (n, (du, de), GB, w, F, sc) = (GB', s')

       Invariant:
       If   GB, Ds |- w : GB
       and  GB, G |- F formula
       and  du = #universal quantifiers in F
       and  de = #existential quantifiers in F
       and  sc is a continuation which
            for all GB, Ds |- s' : GB
            returns s''  of type  GB, Ds, G'[...] |- w'' : GB, G
            and     V''  mapping (GB, Ds, G'[...] |- V  type)  to (GB, Ds |- {G'[...]} V type)
            and     F''  mapping (GB, Ds, G'[...] |- F) to (GB, Ds |- {{G'[...]}} F formula)
       then GB' = GB, Ds'
       and  |Ds'| = de
       and  each declaration in Ds' corresponds to one existential quantifier in F
       and  GB' |- s' : GB
    *)
let rec skolem((du,  , de),  , gB,  , w,  , true,  , sc) (gB,  , w) skolem((du,  , de),  , gB,  , w,  , all (prim d,  , f),  , sc) skolem ((du + 1,  , de),  , gB,  , w,  , f,  , fun (s,  , de') -> (* s'  :  GB, Ds |- s : GB   *)
let let  in(* s'  : GB, Ds, G'[...] |- s' : GB, G *)
(* V'  : maps (GB, Ds, G'[...] |- V type) to (GB, Ds |- {G'[...]} V type) *)
(* F'  : maps (GB, Ds, G'[...] |- F for) to (GB, Ds |- {{G'[...]}} F for) *)
 in (dot1 s',  , (* _   : GB, Ds, G'[...], D[?] |- _ : GB, G, D *)
, fun v -> v' (piDepend ((normalizeDec (d,  , s'),  , meta),  , normalize (v,  , id))),  , (* _   : maps (GB, Ds, G'[....], D[?] |- V : type) to  (GB, Ds, |- {G[....], D[?]} V : type) *)
, fun f -> f' (all (prim (decSub (d,  , s')),  , f)), (* _   : maps (GB, Ds, G'[....], D[?] |- F : for) to  (GB, Ds, |- {{G[....], D[?]}} F : for) *)
)) skolem((du,  , de),  , (g,  , b),  , w,  , ex (dec (name,  , v),  , f),  , sc) let let  in(* s'  : GB, Ds, G'[...] |- s' : GB, G *)
(* V'  : maps  (GB, Ds, G'[...] |- V : type)   to   (GB, Ds |- {G'[...]} V : type) *)
(* F'  : maps  (GB, Ds, G'[...] |- F : for)    to   (GB, Ds |- {{G'[...]}} F : for) *)
let  in(* V1  : GB, Ds, G'[...] |- V1 = V [s'] : type *)
let  in(* V2  : GB, Ds |- {G'[...]} V2 : type *)
let  in(* F1  : GB, Ds, G'[...] |- F1 : for *)
let  in(* F2  : GB, Ds |- {{G'[...]}} F2 : for *)
let  inlet  in(* D2  : GB, Ds |- D2 : type *)
let  in(* T2  : GB, Ds |- T2 : tag *)
 in skolem ((du,  , de + 1),  , (decl (g,  , d2),  , decl (b,  , t2)),  , comp (w,  , shift),  , f,  , fun (s,  , de') -> (* s   : GB, Ds, D2 |- s : GB *)
let let  in(* s'  : GB, Ds, D2, G'[...] |- s' : GB, G *)
(* V'  : maps (GB, Ds, D2, G'[...] |- V type) to (GB, Ds, D2 |- {G'[...]} V type) *)
(* F'  : maps (GB, Ds, D2, G'[...] |- F for) to (GB, Ds, D2 |- {{G'[...]}} F for) *)
 in (dot (exp (root (bVar (du + (de' - de)),  , spine du)),  , s'),  , (* _ : GB, Ds, D2, G'[...] |- s'' : GB, G, D *)
, v',  , f'))(* updateState (S, (Ds, s))

       Invariant:
       G context
       G' |- S state
       G |- Ds new decs
       G' |- s : G
    *)
let rec updateState(s,  , (nil,  , s)) s updateState(s as state (n,  , (g,  , b),  , (iH,  , oH),  , d,  , o,  , h,  , f),  , (lemma (n',  , frl') :: l,  , s)) let let  inlet  in in updateState (state (n,  , (g'',  , b''),  , (iH,  , oH),  , d,  , orderSub (o,  , s'),  , (n',  , forSub (frl',  , s'')) :: map (fun (n',  , f') -> (n',  , forSub (f',  , s'))) h,  , forSub (f,  , s')),  , (l,  , s''))(* selectFormula (n, G, (G0, F, O), S) = S'

       Invariant:
       If   G |- s : G0  and  G0 |- F formula and  G0 |- O order
       and  S is a state
       then S' is the state with
       sc returns with all addition assumptions/residual lemmas for a certain
       branch of the theorem.
    *)
let rec selectFormula(n,  , (g0,  , all (prim (d as dec (_,  , v)),  , f),  , all (_,  , o)),  , s) selectFormula (n,  , (decl (g0,  , d),  , f,  , o),  , s) selectFormula(n,  , (g0,  , and (f1,  , f2),  , and (o1,  , o2)),  , s) let let  in in selectFormula (n,  , (g0,  , f2,  , o2),  , s') selectFormula(nih,  , (gall,  , fex,  , oex),  , s as state (ncurrent,  , (g0,  , b0),  , (_,  , _),  , _,  , ocurrent,  , h,  , f)) let let  in in (nih + 1,  , updateState (s,  , (ds,  , id)))let rec expand(s as state (n,  , (g,  , b),  , (iH,  , oH),  , d,  , o,  , h,  , f)) let let  inlet  in in s'let rec applys (if (! doubleCheck) then isState s else (); s)let rec menu_ "Recursion (calculates ALL new assumptions & residual lemmas)"let rec handleExceptionsfp try  with let  inlet  inlet  in(* local *)
end