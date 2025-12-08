(* QED *)
(* Author: Carsten Schuermann *)

module Qed (Global : GLOBAL)
   (module MetaSyn' : METASYN)
  : QED =
struct
  module MetaSyn = MetaSyn'

  exception Error of string

  local
    module M = MetaSyn
    module I = IntSyn

    fun subgoal (M.State (name, M.Prefix (G, M, B), V)) =
        let
          let rec check = function I.Null -> true
            | (I.Decl (M, M.Top)) -> check M
            | (I.Decl (M, M.Bot)) -> false
        in
          check M
        end

  in
    let subgoal = subgoal
  end (* local *)
end;; (* functor Qed *)
