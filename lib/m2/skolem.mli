(* Skolem administration *)
(* Author: Carsten Schuermann *)

module type SKOLEM =
sig
  (*! module IntSyn : INTSYN !*)

  val install: IntSyn.cid list -> unit
end;  (* module type SKOLEM *)
