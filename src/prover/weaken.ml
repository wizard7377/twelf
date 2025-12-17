Weaken  Whnf WHNF     WEAKEN  struct (*! structure IntSyn = IntSyn' !*)
module (* strengthenExp (U, s) = U'

       Invariant:
       If   G |- s : G'
       and  G |- U : V
       then G' |- U' = U[s^-1] : V [s^-1]
    *)
let rec strengthenExp(u,  , s) normalize (cloInv (u,  , s),  , id)(* strengthenDec (x:V, s) = x:V'

       Invariant:
       If   G |- s : G'
       and  G |- V : L
       then G' |- V' = V[s^-1] : L
    *)
let rec strengthenDec(dec (name,  , v),  , s) dec (name,  , strengthenExp (v,  , s))(* strengthenCtx (G, s) = (G', s')

       If   G0 |- G ctx
       and  G0 |- s G1
       then G1 |- G' = G[s^-1] ctx
       and  G0 |- s' : G1, G'
    *)
let rec strengthenCtx(null,  , s) (null,  , s) strengthenCtx(decl (g,  , d),  , s) let let  in in (decl (g',  , strengthenDec (d,  , s')),  , dot1 s')let rec strengthenSub(s,  , t) compInv (s,  , t)let rec strengthenSpine(nil,  , t) nil strengthenSpine(app (u,  , s),  , t) app (strengthenExp (u,  , t),  , strengthenSpine (s,  , t))let  inlet  inlet  inlet  inlet  inend