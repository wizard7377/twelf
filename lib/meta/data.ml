(* Data aquired during proof search *)

(* Author: Carsten Schuermann *)

module type MTPDATA = sig
  val maxFill : int ref
end

(* signature MTPDATA *)
(* Meta Global parameters *)

(* Author: Carsten Schuermann *)

module MTPData (MTPGlobal : MTPGLOBAL) : MTPDATA = struct
  let maxFill = ref 0
end

(* structure MTPData*)
