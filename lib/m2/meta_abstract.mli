(* Meta Abstraction *)
(* Author: Carsten Schuermann *)

module type METAABSTRACT =
sig
  module MetaSyn : METASYN

  exception Error of string

  val abstract : MetaSyn.State -> MetaSyn.State
end;  (* module type METAABSTRACT *)
