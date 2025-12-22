(* QED *)

(* Author: Carsten Schuermann *)

module Qed (Global : GLOBAL) (MetaSyn' : METASYN) : QED = struct
  module MetaSyn = MetaSyn'

  exception Error of string

  module M = MetaSyn
  module I = IntSyn

  let rec subgoal (M.State (name, M.Prefix (G, M, B), V)) =
    let rec check = function
      | I.Null -> true
      | I.Decl (M, M.Top) -> check M
      | I.Decl (M, M.Bot) -> false
    in
    check M

  let subgoal = subgoal
  (* local *)
end

(* functor Qed *)
