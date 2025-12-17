Init  MetaSyn' METASYN    MetaAbstract METAABSTRACT    MetaAbstract MetaSyn  MetaSyn'    INIT  struct module exception module module (* init c = S'

       Invariant:
       If   c is type constant identifier
       then S' is initial prover state.
    *)
let rec init'cid let let  in in abstract (state ("/" ^ conDecName (sgnLookup cid) ^ "/",  , prefix (null,  , null,  , null),  , v))(* init c1 .. cn = S1 .. Sn

       Invariant:
       If   c1 .. cn are mutually recursive
       then S1 .. Sn is an initial prover state.
    *)
let rec initcidList map init' cidListlet  in(* local *)
end