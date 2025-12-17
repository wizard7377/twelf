Normalize  Whnf WHNF     NORMALIZE  struct (*! structure IntSyn = IntSyn' !*)
(*! structure Tomega = Tomega' !*)
exception module module let rec normalizeFor(all ((d,  , q),  , f),  , t) all ((decSub (d,  , t),  , q),  , normalizeFor (f,  , dot1 t)) normalizeFor(ex ((d,  , q),  , f),  , t) ex ((decSub (d,  , coerceSub t),  , q),  , normalizeFor (f,  , dot1 t)) normalizeFor(and (f1,  , f2),  , t) and (normalizeFor (f1,  , t),  , normalizeFor (f2,  , t)) normalizeFor(fClo (f,  , t1),  , t2) normalizeFor (f,  , comp (t1,  , t2)) normalizeFor(world (w,  , f),  , t) world (w,  , normalizeFor (f,  , t)) normalizeFor(true,  , _) truelet rec whnfFor(ft as (all (d,  , _),  , t)) ft whnfFor(ft as (ex (d,  , f),  , t)) ft whnfFor(ft as (and (f1,  , f2),  , t)) ft whnfFor(fClo (f,  , t1),  , t2) whnfFor (f,  , comp (t1,  , t2)) whnfFor(ft as (world (w,  , f),  , t)) ft whnfFor(ft as (true,  , _)) ft(* normalizePrg (P, t) = (P', t')

       Invariant:
       If   Psi' |- P :: F
       and  Psi  |- t :: Psi'
       and  P doesn't contain free EVars
       then there exists a Psi'', F'
       s.t. Psi'' |- F' for
       and  Psi'' |- P' :: F'
       and  Psi |- t' : Psi''
       and  Psi |- F [t] == F' [t']
       and  Psi |- P [t] == P' [t'] : F [t]
       and  Psi |- P' [t'] :nf: F [t]
    *)
let rec normalizePrg(var n,  , t) (match varSub (n,  , t) with (prg p) -> p (idx _) -> raise (domain) (exp _) -> raise (domain) (block _) -> raise (domain) (undef) -> raise (domain)) normalizePrg(pairExp (u,  , p'),  , t) pairExp (normalize (u,  , coerceSub t),  , normalizePrg (p',  , t)) normalizePrg(pairBlock (b,  , p'),  , t) pairBlock (blockSub (b,  , coerceSub t),  , normalizePrg (p',  , t)) normalizePrg(pairPrg (p1,  , p2),  , t) pairPrg (normalizePrg (p1,  , t),  , normalizePrg (p2,  , t)) normalizePrg(unit,  , _) unit normalizePrg(eVar (_,  , ref (sOME p),  , _),  , t) pClo (p,  , t) normalizePrg(p as eVar _,  , t) pClo (p,  , t) normalizePrg(pClo (p,  , t),  , t') normalizePrg (p,  , comp (t,  , t')) normalizeSpine(nil,  , t) nil normalizeSpine(appExp (u,  , s),  , t) appExp (normalize (u,  , coerceSub t),  , normalizeSpine (s,  , t)) normalizeSpine(appPrg (p,  , s),  , t) appPrg (normalizePrg (p,  , t),  , normalizeSpine (s,  , t)) normalizeSpine(appBlock (b,  , s),  , t) appBlock (blockSub (b,  , coerceSub t),  , normalizeSpine (s,  , t)) normalizeSpine(sClo (s,  , t1),  , t2) normalizeSpine (s,  , comp (t1,  , t2))(*
    and normalizeDec (T.UDec D, t) = T.UDec (I.decSub (D, T.coerceSub t))
(*      | normalizeDec (T.BDec (k, t1), t2) = *)
      | normalizeDec (T.PDec (n, F), t) = T.PDec (n, (normalizeFor (F, t)))
*)
let rec normalizeSub(s as shift n) s normalizeSub(dot (prg p,  , s)) dot (prg (normalizePrg (p,  , id)),  , normalizeSub s) normalizeSub(dot (exp e,  , s)) dot (exp (normalize (e,  , id)),  , normalizeSub s) normalizeSub(dot (block k,  , s)) dot (block k,  , normalizeSub s) normalizeSub(dot (idx k,  , s)) dot (idx k,  , normalizeSub s)let  inlet  inlet  inlet  inend