FunNames  Global GLOBAL    HashTable TABLE   Key String     FUNNAMES  struct (*! structure FunSyn = FunSyn' !*)
exception (****************************************)
(* Constants Names and Name Preferences *)
(****************************************)
(*
     Names (strings) are associated with constants (cids) in two ways:
     (1) There is an array nameArray mapping constants to print names (string),
     (2) there is a hashtable sgnHashTable mapping identifiers (strings) to constants.

     The mapping from constants to their print names must be maintained
     separately from the global signature, since constants which have
     been shadowed must be marked as such when printing.  Otherwise,
     type checking can generate very strange error messages such as
     "Constant clash: c <> c".

     In the same table we also record the fixity property of constants,
     since it is more a syntactic then semantic property which would
     pollute the lambda-calculus core.

     The mapping from identifers (strings) to constants is used during
     parsing.

     There are global invariants which state the mappings must be
     consistent with each other.
  *)
(* nameInfo carries the print name and fixity for a constant *)
type NameInfolet  in(* nameArray maps constants to print names and fixity *)
let  in(* sgnHashTable maps identifiers (strings) to constants (cids) *)
let  inlet  in(* returns optional shadowed entry *)
let  in(* returns optional cid *)
let rec hashClear() clear sgnHashTable(* reset () = ()
       Effect: clear name tables related to constants

       nameArray does not need to be reset, since it is reset individually
       for every constant as it is declared
    *)
let rec reset() (hashClear ())(* override (cid, nameInfo) = ()
       Effect: mark cid as shadowed --- it will henceforth print as %name%
    *)
let rec override(cid,  , nameInfo (name)) update (nameArray,  , cid,  , nameInfo ("%" ^ name ^ "%"))let rec shadownONE () shadow(sOME (_,  , cid)) override (cid,  , sub (nameArray,  , cid))(* installName (name, cid) = ()
       Effect: update mappings from constants to print names and identifiers
               to constants, taking into account shadowing
    *)
let rec installName(name,  , lemma) let let  in(* returns optional shadowed entry *)
 in (update (nameArray,  , lemma,  , nameInfo (name)); shadow shadowed)(* nameLookup (name) = SOME(cid),  if cid has name and is not shadowed,
                         = NONE,   if there is no such constant
    *)
let rec nameLookupname hashLookup name(* constName (cid) = name,
       where `name' is the print name of cid
    *)
let rec constName(cid) (match sub (nameArray,  , cid) with (nameInfo (name)) -> name)(* local ... *)
end