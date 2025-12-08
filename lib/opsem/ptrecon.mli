(* Abstract Machine guided by proof skeleton *)
(* Author: Brigitte Pientks *)
(* Modified: Jeff Polakow *)
(* Modified: Frank Pfenning *)

(* Proof term reconstruction by proof skeleton *)

module type PTRECON =
sig

  (*! module IntSyn : INTSYN !*)
  (*! module CompSyn : COMPSYN !*)


  exception Error of string
  val solve     : CompSyn.pskeleton * (CompSyn.Goal * IntSyn.Sub) * CompSyn.DProg
                  * (CompSyn.pskeleton * IntSyn.exp -> unit) -> unit 

end;; (* module type PTRECON *)
