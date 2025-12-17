TabledSyn  Names NAMES    Table TABLE   Key Int    Index INDEX     TABLEDSYN  struct (*! structure IntSyn = IntSyn' !*)
exception type Tabled(*  datatype ModeSpine = Mnil | Mapp of Marg * ModeSpine
  and  Marg = Marg of Mode * string option
  *)
module let  in(* reset () = ()

       Effect: Resets tabled array
    *)
let rec reset() clear tabledSignature(* installTabled (a, tabled) = ()

       Effect: the tabled is stored with the type family a
    *)
let rec installTableda insert tabledSignature (a,  , false)(* installTabled (a, tabled) = ()

       Effect: the tabled is stored with the type family a
    *)
let rec installKeepTablea ((* Table.delete tabledSignature a; *)
insertShadow tabledSignature (a,  , true); ())(* tablingLookup a = bool

       Looks up whether the predicat a is tabled

    *)
let rec tabledLookupa (match (lookup tabledSignature a) with nONE -> false sOME _ -> true)(* keepTable a = bool

       if we should keep the table for this predicate a
        then returns true
          otherwise false
    *)
let rec keepTablea (match (lookup tabledSignature a) with nONE -> false sOME true -> true sOME false -> false)let  inlet  inlet  inlet  inlet  inend