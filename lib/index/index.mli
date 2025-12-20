(* Indexing *)


(* Author: Carsten Schuermann *)


(* Modified: Frank Pfenning *)


module type INDEX = sig
(*! structure IntSyn : INTSYN !*)
  val reset : unit -> unit
  val resetFrom : IntSyn.cid -> unit
  val install : IntSyn.conDecForm -> IntSyn.head -> unit
(* lookup a = [c1,...,cn] *)
(* c1,...,cn are all constants with target family a *)
(* in order of declaration, defined constants are omitted *)
  val lookup : IntSyn.cid -> IntSyn.head list

end


(* signature INDEX *)

