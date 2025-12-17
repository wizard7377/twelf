TomegaAbstract  Global GLOBAL    Abstract ABSTRACT    Whnf WHNF    Subordinate SUBORDINATE     TOMEGAABSTRACT  struct exception module module module module module let rec shiftCtx(null,  , t) (null,  , t) shiftCtx(decl (g,  , d),  , t) let let  in in (decl (g',  , decSub (d,  , t')),  , dot1 t')(* dotn (t, n) = t'

       Invariant:
       If   Psi0 |- t : Psi
       and  |G| = n   for any G
       then Psi0, G[t] |- t : Psi, G
    *)
let rec dotn(t,  , 0) t dotn(t,  , n) dot1 (dotn (t,  , n - 1))let rec strengthenToSpine(shift _, (* =0 *)
,  , 0,  , (n,  , s)) s strengthenToSpine(dot (idx _, (* = 1 *)
,  , t),  , l,  , (n,  , s)) let let  in in strengthenToSpine (t',  , l - 1,  , (n + 1,  , app (root (bVar n,  , nil),  , s))) strengthenToSpine(dot (undef,  , t),  , l,  , (n,  , s)) strengthenToSpine (t,  , l - 1,  , (n + 1,  , s)) strengthenToSpine(shift k,  , l,  , (n,  , s)) strengthenToSpine (dot (idx (k + 1),  , shift (k + 1)),  , l,  , (n,  , s))(* raiseFor (B, (F, t)) = (P', F'))

       Invariant:
       If   Psi, B, G |-  F for
       and  Psi, G', B' |- t : Psi, B, G
       then Psi, G' |-  F' for
       and  F' = raise (B', F[t])   (using subordination)
    *)
let rec raiseFor(b',  , (true,  , t)) true raiseFor(b',  , (and (f1,  , f2),  , t)) let let  inlet  in in and (f1',  , f2') raiseFor(b',  , (ex ((dec (x,  , v),  , q),  , f),  , t)) let (*        val (w, S) = subweaken (B', 1, I.targetFam V, I.Nil)     *)
let  in(* B'  |- w  : B''    *)
let  in(* B'' |- iw : B'     *)
let  in(* Psi0, G' |- B'' ctx *)
let  in(* Psi0, G' |- V' : type *)
let  in(* Psi, G', x: V' |- B''' ctx *)
let  in(* Psi, G', x: V', B''' |- t'' :   Psi, G', B' *)
(* Psi, G', B' |- t : Psi, B, G  *)
let  in(* Psi, G', x:V', B''' |- t' : Psi, B, G *)
(* Psi, G', x:V', B''' |- w : Psi,G', x:V', B'''' *)
let  in(* Psi, G', x:V', B''' |- S : V' [^|B'''|] >> type  *)
let  in(* Psi, G', x:V', B''' |- U : V[t'] *)
let  in(* Psi, G', x:V', B''' |- t''' :  Psi, B, G, x:V *)
let  in(* Psi, G', x:V' |- F' for*)
 in ex ((dec (x,  , v'),  , q),  , f')(* Psi, G', x:V', B''' |- t''' :  Psi, B, G, x:V *)
 raiseFor(_,  , (all _,  , _)) raise (domain)(* raisePrg (G, P, F) = (P', F'))

       Invariant:
       If   Psi, G |- P in F
       and  Psi |- G : blockctx
       then Psi |- P' in F'
       and  P = raise (G, P')   (using subordination)
       and  F = raise (G, F')   (using subordination)
    *)
let rec raisePrg(g,  , (unit,  , t),  , _) unit raisePrg(g,  , (pairPrg (p1,  , p2),  , t),  , and (f1,  , f2)) let let  inlet  in in pairPrg (p1',  , p2') raisePrg(g,  , (pairExp (u,  , p),  , t),  , ex ((dec (_,  , v),  , _),  , f)) let let  in(* G  |- w  : G'    *)
let  in(* G' |- iw : G     *)
let  in(* Psi0, G' |- B'' ctx *)
let  inlet  in in pairExp (u',  , p')let rec raiseP(g,  , p,  , f) let let  in(*      val P' = T.normalizePrg (P, s) (* G' |- P' : F' *) *)
let  inlet  in in p''let rec raiseF(g,  , (f,  , t)) let let  inlet  in in f'let  inlet  inlet  inlet  inend