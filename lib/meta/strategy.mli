(* MTPStrategy : Version 1.3 *)
(* Author: Carsten Schuermann *)

(* GEN BEGIN SIGNATURE DECLARATION *) signature MTPSTRATEGY = 
sig
  structure StateSyn : STATESYN

  val run : StateSyn.state list -> StateSyn.state list * StateSyn.state list 
              (* open cases -> remaining cases * solved cases *)
end (* GEN END SIGNATURE DECLARATION *);  (* signature MTPSTRATEGY *)
