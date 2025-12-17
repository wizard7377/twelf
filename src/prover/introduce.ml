Introduce  State' STATE    TomegaNames TOMEGANAMES     INTRODUCE  struct (*! structure IntSyn = IntSyn' !*)
(*! structure Tomega = Tomega' !*)
module module module module exception type Operator(*    fun stripTC (T.Abs (_, TC)) = TC *)
let rec stripTCtC tClet rec stripTCOptnONE nONE stripTCOpt(sOME tC) sOME (stripTC tC)let rec stripDec(uDec d) uDec d stripDec(pDec (name,  , f,  , tC1,  , tC2)) pDec (name,  , f,  , tC1,  , stripTCOpt tC2)let rec stripnull null strip(decl (psi,  , d)) decl (strip psi,  , stripDec d)(* expand S = S'

       Invariant:
       If   S = (Psi |> all x1:A1 .... xn: An. F)
       and  F does not start with an all quantifier
       then S' = (Psi, x1:A1, ... xn:An |> F)
    *)
let rec expand(focus (r as eVar (psi,  , r,  , all ((d,  , _),  , f),  , nONE,  , nONE,  , _),  , w)) let let  in in sOME (r,  , lam (d',  , newEVar (decl (strip psi,  , d'),  , f))) expand(focus (r as eVar (psi,  , r,  , ex ((d as dec (_,  , v),  , _),  , f),  , nONE,  , nONE,  , _),  , w)) let let  inlet  in in sOME (r,  , pairExp (x,  , y)) expand(focus (r as eVar (psi,  , r,  , true,  , nONE,  , nONE,  , _),  , w)) (sOME (r,  , unit)) expand(focus (eVar (psi,  , r,  , fClo (f,  , s),  , tC1,  , tC2,  , x),  , w)) expand (focus (eVar (psi,  , r,  , forSub (f,  , s),  , tC1,  , tC2,  , x),  , w)) expand(focus (eVar (psi,  , r,  , _,  , _,  , _,  , _),  , w)) nONE(* apply O = S

       Invariant:
       O = S
    *)
let rec apply(eVar (_,  , r,  , _,  , _,  , _,  , _),  , p) (r := sOME p)(* need to trail for back *)
(* menu O = s

       Invariant:
       s = "Apply universal introduction rules"
    *)
let rec menu(r,  , p) "Intro " ^ nameEVar rexception type Operatorlet  inlet  inlet  inend