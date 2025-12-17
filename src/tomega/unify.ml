TomegaUnify  Abstract ABSTRACT    TypeCheck TYPECHECK    Conv CONV    Normalize NORMALIZE    Whnf WHNF    Print PRINT    TomegaPrint TOMEGAPRINT    Subordinate SUBORDINATE    Weaken WEAKEN     TOMEGAUNIFY  struct (*! structure IntSyn = IntSyn' !*)
(*! structure Tomega = Tomega' !*)
exception module module (* unifyFor (Psi, F1, F2) = R

       Invariant:
       If   F1, F2 contain free variables X1 ... Xn
       and  Psi |- F1 for
       and  Psi |- F2 for
       and  there exists an instantiation I for X1 ...Xn such that
       and  Psi[I] |- F1[I] = F2[I]
       then R = ()
       otherwise exception Unify is raised
    *)
let rec unifyFor(psi,  , f1,  , f2) unifyForN (psi,  , forSub (f1,  , id),  , forSub (f2,  , id)) unifyForN(psi,  , true,  , true) () unifyForN(psi,  , ex ((d1,  , _),  , f1),  , ex ((d2,  , _),  , f2)) (unifyDec (psi,  , uDec d1,  , (uDec d2)); unifyFor (decl (psi,  , uDec d1),  , f1,  , f2)) unifyForN(psi,  , all ((d1,  , _),  , f1),  , all ((d2,  , _),  , f2)) (unifyDec (psi,  , d1,  , d2); unifyFor (decl (psi,  , d1),  , f1,  , f2)) unifyForN(psi,  , fVar (_,  , r),  , f) (r := sOME f) unifyForN(psi,  , f,  , fVar (_,  , r)) (r := sOME f) unifyForN(psi,  , _,  , _) raise (unify "Formula mismatch")(* unifyDec (Psi, D1, D2) = R

       Invariant:
       If   D1, D2 contain free variables X1 ... Xn
       and  Psi |- D1 dec
       and  Psi |- D2 dec
       and  there exists an instantiation I for X1 ...Xn such that
       and  Psi[I] |- D1[I] = D2[I]
       then R = ()
       otherwise exception Unify is raised
    *)
 unifyDec(psi,  , uDec d1,  , uDec d2) if convDec ((d1,  , id),  , (d2,  , id)) then () else raise (unify "Declaration mismatch") unifyDec(psi,  , pDec (_,  , f1),  , pDec (_,  , f2)) unifyFor (psi,  , f1,  , f2)let  inend