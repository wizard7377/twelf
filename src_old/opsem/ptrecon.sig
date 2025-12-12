(* Abstract Machine guided by proof skeleton *)
(* Author: Brigitte Pientks *)
(* Modified: Jeff Polakow *)
(* Modified: Frank Pfenning *)

(* Proof term reconstruction by proof skeleton *)

signature PTRECON =
sig

  (*! structure IntSyn : INTSYN !*)
  (*! structure CompSyn : COMPSYN !*)


  exception Error of string
  val solve     : CompSyn.pskeleton * (CompSyn.goal * IntSyn.sub) * CompSyn.d_prog
                  * (CompSyn.pskeleton * IntSyn.exp -> unit) -> unit 

end;  (* signature PTRECON *)
