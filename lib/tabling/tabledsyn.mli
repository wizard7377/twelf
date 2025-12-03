(* Tabled Syntax *)
(* Author: Brigitte Pientka *)

module type TABLEDSYN =
sig

  (*! module IntSyn : INTSYN !*)

  exception Error of string

  val reset : unit -> unit
  val installTabled : IntSyn.cid  -> unit 
  val installKeepTable : IntSyn.cid  -> unit 

  val tabledLookup : IntSyn.cid -> bool

  val keepTable : IntSyn.cid -> bool

end;  (* module type TABLEDSYN *)
