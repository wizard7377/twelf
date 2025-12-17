Fill  Data DATA    State' STATE    Abstract ABSTRACT    TypeCheck TYPECHECK    Search SEARCH    Search State  State'   Whnf WHNF    Unify UNIFY     FILL  struct (*! structure IntSyn = IntSyn' !*)
(*! structure Tomega = Tomega' !*)
module exception type Operator(* Representation Invariant:  FillWithBVar (X, n) :
           X is an evar GX |- X : VX
           GX |- n : W
           and VX and W are unifiable
       *)
type Operatormodule module module exception (* expand' S = op'

       Invariant:
       If   |- S state
       then op' satifies representation invariant.
    *)
let rec expand(focusLF (y as eVar (r,  , g,  , v,  , _))) let let rec try(vs as (root _,  , _),  , fs,  , o) (try  with ) try((pi ((dec (_,  , v1),  , _),  , v2),  , s),  , fs,  , o) let let  in in try ((v2,  , dot (exp x,  , s)),  , fs,  , o) try((eClo (v,  , s'),  , s),  , fs,  , o) try ((v,  , comp (s',  , s)),  , fs,  , o)(* matchCtx (G, n, Fs) = Fs'

           Invariant:
           If G0 = G, G' and |G'| = n and Fs a list of filling operators that
           satisfy the representation invariant, then Fs' is a list of filling operators
           that satisfy the representation invariant.
        *)
let rec matchCtx(null,  , _,  , fs) fs matchCtx(decl (g,  , dec (x,  , v)),  , n,  , fs) matchCtx (g,  , n + 1,  , try ((v,  , shift (n + 1)),  , fs,  , fillWithBVar (y,  , n + 1))) matchCtx(decl (g,  , nDec _),  , n,  , fs) matchCtx (g,  , n + 1,  , fs)let rec matchSig(nil,  , fs) fs matchSig(const (c) :: l,  , fs) matchSig (l,  , try ((constType (c),  , id),  , fs,  , fillWithConst (y,  , c))) in matchCtx (g,  , 0,  , matchSig (lookup (targetFam v),  , nil))(* apply op = ()

       Invariant:
       If op is a filling operator that satisfies the representation invariant.
       The apply operation is guaranteed to always succeed.
    *)
let rec apply(fillWithBVar (y as eVar (r,  , g,  , v,  , _),  , n)) let (* Invariant : G |- s : G'   G' |- V : type *)
let rec doit(vs as (root _,  , _),  , k) (unify (g,  , vs,  , (v,  , id)); (k nil)) doit((pi ((dec (_,  , v1),  , _),  , v2),  , s),  , k) let let  in in doit ((v2,  , dot (exp x,  , s)),  , (fun s -> k (app (x,  , s)))) doit((eClo (v,  , t),  , s),  , k) doit ((v,  , comp (t,  , s)),  , k)let  in in doit ((w,  , id),  , fun s -> unify (g,  , (y,  , id),  , (root (bVar n,  , s),  , id))) apply(fillWithConst (y as eVar (r,  , g0,  , v,  , _),  , c)) let let rec doit(vs as (root _,  , _),  , k) (unify (g0,  , vs,  , (v,  , id)); (k nil)) doit((pi ((dec (_,  , v1),  , _),  , v2),  , s),  , k) let let  in in doit ((v2,  , dot (exp x,  , s)),  , (fun s -> k (app (x,  , s))))let  in in doit ((w,  , id),  , fun s -> unify (g0,  , (y,  , id),  , (root (const c,  , s),  , id)))(* menu op = s'

       Invariant:
       If op is a filling operator
       then s' is a string describing the operation in plain text
    *)
let rec menu(fillWithBVar (x as eVar (_,  , g,  , _,  , _),  , n)) (match (ctxLookup (ctxName g,  , n)) with dec (sOME x,  , _) -> ("Fill " ^ evarName (g,  , x) ^ " with variable " ^ x)) menu(fillWithConst (x as eVar (_,  , g,  , _,  , _),  , c)) ("Fill " ^ evarName (g,  , x) ^ " with constant " ^ conDecName (sgnLookup c))let  inlet  inlet  in(* local *)
end