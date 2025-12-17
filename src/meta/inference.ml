Inference  MTPGlobal MTPGLOBAL    StateSyn' STATESYN    Abstract ABSTRACT    TypeCheck TYPECHECK    FunTypeCheck FUNTYPECHECK    FunTypeCheck StateSyn  StateSyn'   UniqueSearch UNIQUESEARCH    UniqueSearch StateSyn  StateSyn'   Print PRINT    Whnf WHNF     INFERENCE  struct (*! structure FunSyn = FunSyn' !*)
module exception type Operatormodule module module exception (* createEVars (G, (F, V, s)) = (Xs', (F', V', s'))

       Invariant:
       If   |- G ctx
       and  G0 |- F = {{x1:A1}} .. {{xn::An}} F1 formula
       and  G0 |- V = { x1:A1}  .. {xn:An} V1 : type
       and  G |- s : G0
       then Xs' = (X1', .., Xn') a list of EVars
       and  G |- Xi' : A1 [X1'/x1..X(i-1)'/x(i-1)]          for all i <= n
       and  G |- s: G'
       and  G0 |- F' = F1 for
       and  G0 |- V' = V1 : type
    *)
let rec createEVars(g,  , (pi ((dec (_,  , v),  , meta),  , v'),  , s)) let let  inlet  inlet  in in (x' :: xs,  , fVs') createEVars(g,  , fVs as (_,  , s)) (nil,  , fVs)(* forward (G, B, (V, F)) = (V', F')  (or none)

       Invariant:
       If   |- G ctx
       and  G |- B tags
       and  G |- V type
       and  G; . |- F : formula
       then G |- V' type
       and  G; . |- F' : formula

    *)
let rec forward(g,  , b,  , v as pi ((_,  , meta),  , _)) let let  inlet  in in try  with  forward(g,  , b,  , v) nONE(* expand' ((G, B), n) = ((Gnew, Bnew), sc)

       Invariant:
       If   |- G0 ctx    G0 |- B0 tags
       and  |- G ctx     G |- B tags
       and  G prefix of G0 , and B prefix of B0
       and  n + |G| = |G0|
       then sc is a continutation which maps
            |- G' ctx
            and G' |- B' tags
            and G', B' |- w' : G0, B0
            to  |- G'' ctx
            and G'' |- B'' tags
            and G'', B'' extends G, B
       and |- Gnew = G ctx
       and Gnew |- Bnew tags
       where Bnew stems from B where all used lemmas (S.RL) are now tagged with (S.RLdone)
    *)
let rec expand'((g0,  , b0),  , (null,  , null),  , n) ((null,  , null),  , fun ((g',  , b'),  , w') -> ((g',  , b'),  , w')) expand'((g0,  , b0),  , (decl (g,  , d as dec (_,  , v)),  , decl (b,  , t as lemma (rL))),  , n) let let  inlet  inlet  in in match (forward (g0,  , b0,  , (vs))) with nONE -> ((decl (g0',  , d),  , decl (b0',  , t)),  , sc') sOME (v') -> ((decl (g0',  , d),  , decl (b0',  , lemma (rLdone))),  , fun ((g',  , b'),  , w') -> let let  in(* G' |- V'' : type *)
 in sc' ((decl (g',  , dec (nONE,  , v'')),  , decl (b',  , lemma (splits (! maxSplit)))),  , comp (w',  , shift))) expand'(gB0,  , (decl (g,  , d),  , decl (b,  , t)),  , n) let let  in in ((decl (g0',  , d),  , decl (b0',  , t)),  , sc')(* expand' S = op'

       Invariant:
       If   |- S state
       then op' is an operator which performs the filling operation
    *)
let rec expand(s as state (n,  , (g,  , b),  , (iH,  , oH),  , d,  , o,  , h,  , f)) let let  inlet  inlet  inlet  inlet  inlet  inlet  in in fun () -> s'(* apply op = B'

       Invariant:
       If op is a filling operator
       then B' holds iff the filling operation was successful
    *)
let rec applyf f ()(* menu op = s'

       Invariant:
       If op is a filling operator
       then s' is a string describing the operation in plain text
    *)
let rec menu_ "Inference"let  inlet  inlet  in(* local *)
end