(* Names of Constants and Variables *)


(* Author: Carsten Schuermann *)


module FunNames (Global : GLOBAL) : FUNNAMES = struct (*! structure FunSyn = FunSyn' !*)

exception Error of string
(****************************************)

(* Constants Names and Name Preferences *)

(****************************************)

(*
     Names (strings) are associated with constants (cids) in two ways:
     (1) There is an array nameArray mapping constants to print names (string),
     (2) there is a hashtable sgnHashTable mapping identifiers (strings) to constants.

     The mapping from constants to their print names must be maintained
     separately from the global signature, since constants which have
     been shadowed must be such when printing.  Otherwise,
     type checking can generate very strange error messages "Constant clash: c <> c".

     In the same table we also record the fixity property of constants,
     since it is more a syntactic then semantic property which would
     pollute the lambda-calculus core.

     The mapping from identifers (strings) to constants is used during
     parsing.

     There are global invariants which state the mappings must be
     consistent with each other.
  *)

(* nameInfo carries the print name and fixity for_sml a constant *)

type nameInfo = NameInfo of string
let maxCid = Global.maxCid
(* nameArray maps constants to print names and fixity *)

let nameArray = (Array.array (maxCid + 1, NameInfo "") : nameInfo Array.array)
(* sgnHashTable maps identifiers (strings) to constants (cids) *)

let sgnHashTable : IntSyn.cid HashTable.table = HashTable.new_ (4096)
let hashInsert = HashTable.insertShadow sgnHashTable
(* returns optional shadowed entry *)

let hashLookup = HashTable.lookup sgnHashTable
(* returns optional cid *)

let rec hashClear ()  = HashTable.clear sgnHashTable
(* reset () = ()
       Effect: clear name tables related to constants

       nameArray does not need to be reset, since it is reset individually
       for_sml every it is declared
    *)

let rec reset ()  = (hashClear ())
(* override (cid, nameInfo) = ()
       Effect: mark shadowed --- it will henceforth %name%
    *)

let rec override (cid, NameInfo (name))  = (* should shadowed identifiers keep their fixity? *)
 Array.update (nameArray, cid, NameInfo ("%" ^ name ^ "%"))
let rec shadow = function None -> () | (Some (_, cid)) -> override (cid, Array.sub (nameArray, cid))
(* installName (name, cid) = ()
       Effect: update mappings from constants to print names and identifiers
               to constants, taking into account shadowing
    *)

let rec installName (name, lemma)  = ( (* returns optional shadowed entry *)
let shadowed = hashInsert (name, lemma) in  (Array.update (nameArray, lemma, NameInfo (name)); shadow shadowed) )
(* nameLookup (name) = SOME(cid),  if cid has name and is not shadowed,
                         = NONE,   if there is no such constant
    *)

let rec nameLookup name  = hashLookup name
(* constName (cid) = name,
       where `name' is the print name of cid
    *)

let rec constName (cid)  = (match Array.sub (nameArray, cid) with (NameInfo (name)) -> name)
(* local ... *)

 end


(* functor Names *)

