Filling  MetaSyn' METASYN    MetaAbstract METAABSTRACT    MetaAbstract MetaSyn  MetaSyn'   Search OLDSEARCH    Search MetaSyn  MetaSyn'   Whnf WHNF    Print PRINT     FILLING  struct module exception exception type Operatormodule module exception let rec delay(search,  , params)() (try  with )let rec makeAddressInitsk (s,  , k)let rec makeAddressContmakeAddressk makeAddress (k + 1)(* operators (G, GE, (V, s), abstract, makeAddress) = (OE', OL')

       Invariant:
       If   G |- s : G1   G1 |- V : type
       and  abstract is an abstraction continuation
       and  makeAddress is continuation which calculates the correct
         debruijn index of the variable being filled
       and V = {V1}...{Vn} V'
       then OE' is an operator list, OL' is a list with one operator
         where the ith O' in OE' corresponds to a function which generates ALL possible
                                      successor states instantiating - non-index variables
                                      with terms (if possible) in Vi
        and OL' is a list containing one operator which instantiates all - non-index variables
          in V' with the smallest possible terms.
    *)
let rec operators(g,  , gE,  , vs,  , abstractAll,  , abstractEx,  , makeAddress) operatorsW (g,  , gE,  , whnf vs,  , abstractAll,  , abstractEx,  , makeAddress) operatorsW(g,  , gE,  , vs as (root (c,  , s),  , _),  , abstractAll,  , abstractEx,  , makeAddress) (nil,  , (makeAddress 0,  , delay (fun params -> (try  with ),  , (g,  , gE,  , vs,  , abstractEx)))) operatorsW(g,  , gE,  , (pi ((d as dec (_,  , v1),  , p),  , v2),  , s),  , abstractAll,  , abstractEx,  , makeAddress) let let  in in ((makeAddress 0,  , delay (searchAll,  , (g,  , gE,  , (v1,  , s),  , abstractAll))) :: gO',  , o)(* createEVars (G, M) = ((G', M'), s', GE')

       Invariant:
       If   |- G ctx
       and  G |- M mtx
       then |- G' ctx
       and  G' |- M' mtx
       and  G' |- s' : G
       and  GE a list of EVars

    *)
let rec createEVars(prefix (null,  , null,  , null)) (prefix (null,  , null,  , null),  , id,  , nil) createEVars(prefix (decl (g,  , d),  , decl (m,  , top),  , decl (b,  , b))) let let  in in (prefix (decl (g',  , decSub (d,  , s')),  , decl (m',  , top),  , decl (b',  , b)),  , dot1 s',  , gE') createEVars(prefix (decl (g,  , dec (_,  , v)),  , decl (m,  , bot),  , decl (b,  , _))) let let  inlet  inlet  in in (prefix (g',  , m',  , b'),  , dot (exp (x),  , s'),  , x' :: gE')(* expand' ((G, M), V) = (OE', OL')

       Invariant:
       If   |- G ctx
       and  G |- M mtx
       and  G |- V type
       and  V = {V1}...{Vn} V'
       then OE' is an operator list, OL' is a list with one operator
         where the ith O' in OE' corresponds to a function which generates ALL possible
                                      successor states instantiating - non-index variables
                                      with terms (if possible) in Vi
        and OL' is a list containing one operator which instantiates all - non-index variables
          in V' with the smallest possible terms.
    *)
let rec expand(s as state (name,  , prefix (g,  , m,  , b),  , v)) let let  inlet rec abstractAllacc (try  with )let rec abstractEx() try  with  in operators (g',  , gE',  , (v,  , s'),  , abstractAll,  , abstractEx,  , makeAddressInit s)(* apply (S, f) = S'

       Invariant:
       S is state and f is a function constructing the successor state S'
    *)
let rec apply(_,  , f) f ()let rec menu((state (name,  , prefix (g,  , m,  , b),  , v),  , k),  , sl) let let rec toString(g,  , pi ((dec (_,  , v),  , _),  , _),  , 0) expToString (g,  , v) toString(g,  , v as root _,  , 0) expToString (g,  , v) toString(g,  , pi ((d,  , _),  , v),  , k) toString (decl (g,  , d),  , v,  , k - 1)(* no cases for
              toSTring (G, I.Root _, k) for k <> 0
            *)
 in "Filling   : " ^ toString (g,  , v,  , k)let  inlet  inlet  in(* local *)
end