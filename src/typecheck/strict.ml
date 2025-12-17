Strict  Whnf WHNF     STRICT  struct (*! structure IntSyn = IntSyn' !*)
(*! structure Paths = Paths' !*)
exception module (* Definition of normal form (nf) --- see lambda/whnf.fun *)
(* patSpine (k, S) = B

       Invariant:
       If  G, D |- S : V > V', S in nf
       and |D| = k
       then B iff S = (k1 ; k2 ;...; kn ; NIL), kn <= k, all ki pairwise distinct
    *)
let rec patSpine(_,  , nil) true patSpine(k,  , app (root (bVar (k'),  , nil),  , s)) let let rec indexDistinct(nil) true indexDistinct(app (root (bVar (k''),  , nil),  , s)) k' <> k'' && indexDistinct s indexDistinct_ false in k' <= k && patSpine (k,  , s) && indexDistinct s patSpine_ false(* strictExp (k, p, U) = B

       Invariant:
       If  G, D |- U : V
       and U is in nf (normal form)
       and |D| = k
       then B iff U is strict in p
    *)
let rec strictExp(_,  , _,  , uni _) false strictExp(k,  , p,  , lam (d,  , u)) strictDec (k,  , p,  , d) || strictExp (k + 1,  , p + 1,  , u) strictExp(k,  , p,  , pi ((d,  , _),  , u)) strictDec (k,  , p,  , d) || strictExp (k + 1,  , p + 1,  , u) strictExp(k,  , p,  , root (h,  , s)) (match h with (bVar (k')) -> if (k' = p) then patSpine (k,  , s) else if (k' <= k) then strictSpine (k,  , p,  , s) else false (const (c)) -> strictSpine (k,  , p,  , s) (def (d)) -> strictSpine (k,  , p,  , s) (fgnConst (cs,  , conDec)) -> strictSpine (k,  , p,  , s)) strictExp(k,  , p,  , fgnExp (cs,  , ops)) false(* this is a hack - until we investigate this further   -rv *)
(* no other cases possible *)
(* strictSpine (k, S) = B

       Invariant:
       If  G, D |- S : V > W
       and S is in nf (normal form)
       and |D| = k
       then B iff S is strict in k
    *)
 strictSpine(_,  , _,  , nil) false strictSpine(k,  , p,  , app (u,  , s)) strictExp (k,  , p,  , u) || strictSpine (k,  , p,  , s) strictDec(k,  , p,  , dec (_,  , v)) strictExp (k,  , p,  , v)(* strictArgParm (p, U) = B

       Traverses the flexible abstractions in U.

       Invariant:
       If   G |- U : V
       and  G |- p : V'
       and  U is in nf
       then B iff argument parameter p occurs in strict position in U
                  which starts with argument parameters
    *)
let rec strictArgParm(p,  , u as root _) strictExp (0,  , p,  , u) strictArgParm(p,  , u as pi _) strictExp (0,  , p,  , u) strictArgParm(p,  , u as fgnExp _) strictExp (0,  , p,  , u) strictArgParm(p,  , lam (d,  , u)) strictArgParm (p + 1,  , u)let rec occToString(sOME (ocd),  , occ) wrap (occToRegionDef1 ocd occ,  , "") occToString(nONE,  , occ) "Error: "let rec decToVarName(dec (nONE,  , _)) "implicit variable" decToVarName(dec (sOME (x),  , _)) "variable " ^ x(* strictTop ((U, V), ocdOpt) = ()

       Invariant:
       condec has form c = U : V where . |- U : V
       and U is in nf (normal form)
       then function returns () if U every argument parameter of U
            has at least one strict and rigid occurrence in U
       raises Error otherwise

       ocdOpt is an optional occurrence tree for condec for error messages
    *)
let rec strictTop((u,  , v),  , ocdOpt) let let rec strictArgParms(root (bVar _,  , _),  , _,  , occ) raise (error (occToString (ocdOpt,  , occ) ^ "Head not rigid, use %abbrev")) strictArgParms(root _,  , _,  , _) () strictArgParms(pi _,  , _,  , _) () strictArgParms(fgnExp _,  , _,  , _) () strictArgParms(lam (d,  , u'),  , pi (_,  , v'),  , occ) if strictArgParm (1,  , u') then strictArgParms (u',  , v',  , body occ) else raise (error (occToString (ocdOpt,  , occ) ^ "No strict occurrence of " ^ decToVarName d ^ ", use %abbrev")) strictArgParms(u as lam _,  , v as root (def _,  , _),  , occ) strictArgParms (u,  , normalize (expandDef (v,  , id)),  , occ) in strictArgParms (u,  , v,  , top)let rec occursInType((i,  , v),  , ocdOpt) let let rec oit((0,  , v),  , occ) () oit((i,  , pi ((d,  , p),  , v)),  , occ) (match piDepend ((d,  , p),  , v) with pi ((d',  , maybe),  , v) -> oit ((i - 1,  , v),  , body occ) _ -> raise (error (occToString (ocdOpt,  , occ) ^ "No occurrence of " ^ decToVarName d ^ " in type, use %abbrev"))) oit_ () in oit ((i,  , v),  , top)let  inlet  inend