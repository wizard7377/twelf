(* Strategy *)
(* Author: Carsten Schuermann *)

signature STRATEGY = 
sig
  structure MetaSyn : METASYN

  val run : MetaSyn.state list -> MetaSyn.state list * MetaSyn.state list 
              (* open cases -> remaining cases * solved cases *)

end;  (* signature STRATEGY *)
