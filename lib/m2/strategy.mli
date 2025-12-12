(* Strategy *)
(* Author: Carsten Schuermann *)

(* GEN BEGIN SIGNATURE DECLARATION *) signature STRATEGY = 
sig
  structure MetaSyn : METASYN

  val run : MetaSyn.state list -> MetaSyn.state list * MetaSyn.state list 
              (* open cases -> remaining cases * solved cases *)

end (* GEN END SIGNATURE DECLARATION *);  (* signature STRATEGY *)
