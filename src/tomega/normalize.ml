Normalize  IntSyn' INTSYN    Tomega' TOMEGA    Tomega' IntSyn  IntSyn'   Whnf WHNF    Whnf IntSyn  IntSyn'    NORMALIZE  struct module module exception module module let rec normalizeFor(all (d,  , f),  , t) all (decSub (d,  , t),  , normalizeFor (f,  , dot1 t)) normalizeFor(ex (d,  , f),  , t) ex (decSub (d,  , coerceSub t),  , normalizeFor (f,  , dot1 t)) normalizeFor(and (f1,  , f2),  , t) and (normalizeFor (f1,  , t),  , normalizeFor (f2,  , t)) normalizeFor(fClo (f,  , t1),  , t2) normalizeFor (f,  , comp (t1,  , t2)) normalizeFor(world (w,  , f),  , t) world (w,  , normalizeFor (f,  , t)) normalizeFor(true,  , _) true(* normalizePrg (P, t) = (P', t')

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
let rec normalizePrg(p as (root (const _,  , _)),  , t) p normalizePrg((p as (root (var n,  , _))),  , t) normalizePrg (p,  , dot (varSub (n,  , t),  , id)) normalizePrg(lam (d,  , p'),  , t) lam (d,  , normalizePrg (p',  , dot1 t)) normalizePrg(pairExp (u,  , p'),  , t) pairExp (eClo (whnf ((u,  , coerceSub t) :  Eclo)),  , normalizePrg (p',  , t)) normalizePrg(pairPrg (p1,  , p2),  , t) pairPrg (normalizePrg (p1,  , t),  , normalizePrg (p2,  , t)) normalizePrg(unit,  , _) unit normalizePrg(redex (p,  , s),  , t) redex (normalizePrg (p,  , t),  , normalizeSpine s) normalizePrg(rec (d,  , p),  , t) rec (d,  , normalizePrg (p,  , t)) normalizePrg(p as case _,  , t) p normalizePrg(p as eVar (psi,  , ref (sOME p'),  , _),  , t) normalizePrg (p',  , t) normalizeSpinenil nil normalizeSpine(appExp (u,  , s)) appExp (u,  , normalizeSpine s) normalizeSpine(appPrg (p,  , s)) appPrg (normalizePrg (p,  , id),  , normalizeSpine s) normalizeSpine(appBlock (b,  , s)) appBlock (b,  , normalizeSpine s)(*
    and normalizeDec (T.UDec D, t) = T.UDec (I.decSub (D, T.coerceSub t))
(*      | normalizeDec (T.BDec (k, t1), t2) = *)
      | normalizeDec (T.PDec (n, F), t) = T.PDec (n, (normalizeFor (F, t)))
*)
let rec normalizeSub(s as shift n) s normalizeSub(dot (prg p,  , s)) dot (prg (normalizePrg (p,  , id)),  , normalizeSub s) normalizeSub(dot (f,  , s)) dot (f,  , normalizeSub s)let  inlet  inlet  inlet  inend