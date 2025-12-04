(* Strategy *)
(* Author: Carsten Schuermann *)

module type STRATEGY = 
sig
  module MetaSyn : METASYN

  val run : MetaSyn.state list -> MetaSyn.state list * MetaSyn.state list 
              (* open cases -> remaining cases * solved cases *)

end;  (* module type STRATEGY *)
