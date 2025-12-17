Elim  Data DATA    State' STATE    Abstract ABSTRACT    TypeCheck TYPECHECK    Whnf WHNF    Unify UNIFY     ELIM  struct (*! structure IntSyn = IntSyn' !*)
(*! structure Tomega = Tomega' !*)
module exception type Operatortype Operatormodule module module exception (* These lines need to move *)
(* fun stripTC (T.Abs (_, TC)) = TC *)
let rec stripTCtC tClet rec stripTCOptnONE nONE stripTCOpt(sOME tC) sOME (stripTC tC)let rec stripDec(uDec d) uDec d stripDec(pDec (name,  , f,  , tC1,  , tC2)) pDec (name,  , f,  , tC1,  , stripTCOpt tC2)let rec stripnull null strip(decl (psi,  , d)) decl (strip psi,  , stripDec d)(* expand' S = op'

       Invariant:
       If   |- S state
       then op' is an operator which performs the filling operation
    *)
let rec expand(focus (y as eVar (psi,  , r,  , g,  , v,  , _,  , _),  , w)) let let rec matchCtx(null,  , _,  , fs) fs matchCtx(decl (g,  , pDec (x,  , f,  , _,  , _)),  , n,  , fs) matchCtx (g,  , n + 1,  , local (y,  , n) :: fs) matchCtx(decl (g,  , uDec _),  , n,  , fs) matchCtx (g,  , n + 1,  , fs) in matchCtx (psi,  , 1,  , nil)(* apply op = B'

       Invariant:
       If op is a filling operator
       then B' holds iff the filling operation was successful
    *)
let rec apply(local (r as eVar (psi,  , r,  , g,  , nONE,  , nONE,  , _),  , n)) let let  in in (match f0 with all ((uDec (dec (_,  , v)),  , _),  , f) -> let let  inlet  inlet  in(* the NONE, NONE may breach an invariant *)
(* revisit when we add subterm orderings *)
let  inlet  in in (r := sOME (let (d,  , redex (var n,  , appExp (x,  , nil)),  , y))) ex ((d1,  , _),  , f) -> let let  inlet  inlet  inlet  inlet  inlet  in in (r := sOME (letPairExp (d1',  , d2,  , var n,  , y))) true -> let let  in in (r := sOME (letUnit (var n,  , y)))) apply(local (eVar (psi,  , r,  , fClo (f,  , s),  , tC1,  , tC2,  , x),  , n)) apply (local (eVar (psi,  , r,  , forSub (f,  , s),  , tC1,  , tC2,  , x),  , n))(* menu op = s'

       Invariant:
       If op is a filling operator
       then s' is a string describing the operation in plain text
    *)
let rec menu(local (x as eVar (psi,  , _,  , _,  , _,  , _,  , _),  , n)) (match (ctxLookup (psi,  , n)) with pDec (sOME x,  , _,  , _,  , _) -> ("Elim " ^ nameEVar x ^ " with variable " ^ x))(* Invariant: Context is named  --cs Fri Mar  3 14:31:08 2006 *)
let  inlet  inlet  in(* local *)
end