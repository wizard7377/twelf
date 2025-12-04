(* Tabled Syntax *)
(* Author: Brigitte Pientka *)

let recctor TabledSyn ((*! module IntSyn' : INTSYN !*)
                 module Names : NAMES
                 (*! sharing Names.IntSyn = IntSyn' !*)
                 module Table : TABLE where type key = int
                 module Index : INDEX
                 (*! sharing Index.IntSyn = IntSyn' !*)
                     ) : TABLEDSYN =
struct
  (*! module IntSyn = IntSyn' !*)

  exception Error of string

  type tabled = yes | no

(*  type ModeSpine = Mnil | Mapp of Marg * ModeSpine
  and  Marg = Marg of Mode * string option
  *)
  local
    module I = IntSyn

    let tabledSignature : bool Table.Table = Table.new(0);

    (* reset () = ()

       Effect: Resets tabled array
    *)

    fun reset () = Table.clear tabledSignature

    (* installTabled (a, tabled) = ()

       Effect: the tabled is stored with the type family a
    *)
    fun installTabled a = Table.insert tabledSignature (a, false)

    (* installTabled (a, tabled) = ()

       Effect: the tabled is stored with the type family a
    *)

    fun installKeepTable a =
      ((* Table.delete tabledSignature a; *)
       Table.insertShadow tabledSignature (a, true);())


    (* tablingLookup a = bool

       Looks up whether the predicat a is tabled

    *)

    fun tabledLookup a =
     (case (Table.lookup tabledSignature a) of
       NONE => false
     | SOME _ => true)


    (* keepTable a = bool

       if we should keep the table for this predicate a
        then returns true
          otherwise false
    *)

    fun keepTable a =
     (case (Table.lookup tabledSignature a) of
       NONE => false
     | SOME true => true
     | SOME false => false)

  in
    let reset = reset
    let installTabled = installTabled
    let installKeepTable =  installKeepTable
    let tabledLookup = tabledLookup
    let keepTable = keepTable
  end
end;  (* functor TabledSyn *)
