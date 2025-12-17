Lemma  MetaSyn' METASYN    MetaAbstract METAABSTRACT    MetaAbstract MetaSyn  MetaSyn'    LEMMA  struct module exception module module module (* createEVars (G, M, B) = ((G', M', B'), s')

       Invariant:
       If   |- G ctx
       then |- G' ctx
       and  . |- s' : G
       M and B are mode and bound contexts matching G, and similarly for M' and B'.
    *)
let rec createEVars(prefix (null,  , null,  , null)) (prefix (null,  , null,  , null),  , id) createEVars(prefix (decl (g,  , d),  , decl (m,  , top),  , decl (b,  , b))) let let  in in (prefix (decl (g',  , decSub (d,  , s')),  , decl (m',  , top),  , decl (b',  , b)),  , dot1 s') createEVars(prefix (decl (g,  , dec (_,  , v)),  , decl (m,  , bot),  , decl (b,  , _))) let let  inlet  in in (prefix (g',  , m',  , b'),  , dot (exp (x),  , s'))(* apply (((G, M), V), a) = ((G', M'), V')

       Invariant:
       If   |- G ctx
       and  G |- M mtx
       and  a is a type constant of type Va: Sigma (a) = Va
       then |- G' ctx
       and  G' |- M' mtx
       and  G' |- S' : Va > type
       and  G' |- s' : G
       and  G' |- V' = {a S'}. V[s' o ^]
       and  ((G', M'), V') is a state
    *)
let rec apply(state (name,  , gM,  , v),  , a) let let  inlet  in(* Vs' = type *)
 in abstract (state (name,  , gM',  , pi ((dec (nONE,  , u'),  , no),  , eClo (v,  , comp (s',  , shift)))))let  in(* local *)
end