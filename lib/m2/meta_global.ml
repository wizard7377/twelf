open Basis
(* Global parameters *)

(* Author: Carsten Schuermann *)

module type METAGLOBAL = sig
  type strategy = RFS | FRS

  val strategy : strategy ref
  val maxFill : int ref
  val maxSplit : int ref
  val maxRecurse : int ref
end

(* signature METAGLOBAL *)
(* Global parameters *)

(* Author: Carsten Schuermann *)

module MetaGlobal : METAGLOBAL = struct
  type strategy = RFS | FRS

  let strategy = ref FRS
  let maxFill = ref 6
  let maxSplit = ref 2
  let maxRecurse = ref 10
end

(* structure MetaGlobal *)
