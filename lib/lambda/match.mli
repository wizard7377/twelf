(* Matching *)

(* Author: Frank Pfenning, Carsten Schuermann *)

module type MATCH = sig
  (*! structure IntSyn : INTSYN !*)
  (* matching *)
  exception Match of string

  val match_ : IntSyn.dctx * IntSyn.eclo * IntSyn.eclo -> unit

  (* raises Unify *)
  val matchW : IntSyn.dctx * IntSyn.eclo * IntSyn.eclo -> unit

  (* raises Unify *)
  val matchBlock : IntSyn.dctx * IntSyn.block * IntSyn.block -> unit

  (* raises Unify *)
  val matchSub : IntSyn.dctx * IntSyn.sub * IntSyn.sub -> unit

  (* raises Unify *)
  (* instance (G, Us,Us') will instantiate an effect 
     checks if Us' is an instance of Us *)
  val instance : IntSyn.dctx * IntSyn.eclo * IntSyn.eclo -> bool

  (* instance' (G, Us,Us') is like instance, but returns NONE for_sml
     success and SOME(msg) for_sml failure *)
  val instance' : IntSyn.dctx * IntSyn.eclo * IntSyn.eclo -> string option
end

(* signature MATCH *)
