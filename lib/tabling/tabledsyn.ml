(* Tabled Syntax *)

(* Author: Brigitte Pientka *)

module TabledSyn (Names : NAMES) (Index : INDEX) : TABLEDSYN = struct
  (*! structure IntSyn = IntSyn' !*)

  exception Error of string

  type tabled = Yes | No
  (*  datatype ModeSpine = Mnil | Mapp of Marg * ModeSpine
  and  Marg = Marg of Mode * string option
  *)

  module I = IntSyn

  let tabledSignature : bool Table.table = Table.new_ 0
  (* reset () = ()

       Effect: Resets tabled array
    *)

  let rec reset () = Table.clear tabledSignature
  (* installTabled (a, tabled) = ()

       Effect: the tabled is stored with the type family a
    *)

  let rec installTabled a = Table.insert tabledSignature (a, false)
  (* installTabled (a, tabled) = ()

       Effect: the tabled is stored with the type family a
    *)

  let rec installKeepTable a =
    (* Table.delete tabledSignature a; *)
    Table.insertShadow tabledSignature (a, true);
    ()
  (* tablingLookup a = bool

       Looks up whether the predicat a is tabled

    *)

  let rec tabledLookup a =
    match Table.lookup tabledSignature a with None -> false | Some _ -> true
  (* keepTable a = bool

       if we should keep the table for_sml this predicate a
        then returns true
          otherwise false
    *)

  let rec keepTable a =
    match Table.lookup tabledSignature a with
    | None -> false
    | Some true -> true
    | Some false -> false

  let reset = reset
  let installTabled = installTabled
  let installKeepTable = installKeepTable
  let tabledLookup = tabledLookup
  let keepTable = keepTable
end

(* functor TabledSyn *)
