MetaSyn  Whnf WHNF     METASYN  struct (*! structure IntSyn = IntSyn' !*)
exception type Vartype Mode(*     | Top                  *)
type Prefix(* Btx splitting depths       *)
type State(*             |- V           *)
type Sgn(*      | c:V, IS             *)
module (* createEVarSpineW (G, (V, s)) = ((V', s') , S')

       Invariant:
       If   G |- s : G1   and  G1 |- V = Pi {V1 .. Vn}. W : L
       and  G1, V1 .. Vn |- W atomic
       then G |- s' : G2  and  G2 |- V' : L
       and  S = X1; ...; Xn; Nil
       and  G |- W [1.2...n. s o ^n] = V' [s']
       and  G |- S : V [s] >  V' [s']
    *)
let rec createEVarSpine(g,  , vs) createEVarSpineW (g,  , whnf vs) createEVarSpineW(g,  , vs as (uni type,  , s)) (nil,  , vs) createEVarSpineW(g,  , vs as (root _,  , s)) (nil,  , vs) createEVarSpineW(g,  , (pi ((d as dec (_,  , v1),  , _),  , v2),  , s)) let let  inlet  in in (app (x,  , s),  , vs)(* createAtomConst (G, c) = (U', (V', s'))

       Invariant:
       If   S |- c : Pi {V1 .. Vn}. V
       then . |- U' = c @ (Xn; .. Xn; Nil)
       and  . |- U' : V' [s']
    *)
let rec createAtomConst(g,  , h) let let  inlet  inlet  in in (root (h,  , s),  , vs)(* createAtomBVar (G, k) = (U', (V', s'))

       Invariant:
       If   G |- k : Pi {V1 .. Vn}. V
       then . |- U' = k @ (Xn; .. Xn; Nil)
       and  . |- U' : V' [s']
    *)
let rec createAtomBVar(g,  , k) let let  inlet  in in (root (bVar (k),  , s),  , vs)let  inlet  inend