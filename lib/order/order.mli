(* Termination Order *)


(* Author: Carsten Schuermann *)


module type ORDER = sig
(*! structure IntSyn : INTSYN !*)
  exception Error of string
  type 'a order = Arg of 'a | Lex of 'a order list | Simul of 'a order list
(*     | [O1 .. On]           *)
  type predicate = Less of int order * int order | Leq of int order * int order | Eq of int order * int order
(* O = O'                     *)
  type mutual = Empty | LE of IntSyn.cid * mutual | LT of IntSyn.cid * mutual
(*     | lex order for_sml  -     *)
  type tDec = TDec of int order * mutual
  type rDec = RDec of predicate * mutual
  val reset : unit -> unit
  val resetROrder : unit -> unit
  val install : IntSyn.cid * tDec -> unit
  val uninstall : IntSyn.cid -> bool
  val installROrder : IntSyn.cid * rDec -> unit
  val uninstallROrder : IntSyn.cid -> bool
  val selLookup : IntSyn.cid -> int order
  val selLookupROrder : IntSyn.cid -> predicate
  val mutLookup : IntSyn.cid -> mutual
  val closure : IntSyn.cid -> IntSyn.cid list

end


(* signature ORDER *)

