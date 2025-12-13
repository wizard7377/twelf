(* QED *)
(* Author: Carsten Schuermann *)

functor (* GEN BEGIN FUNCTOR DECL *) Qed (structure Global : GLOBAL
             structure MetaSyn' : METASYN)
  : QED =
struct
  structure MetaSyn = MetaSyn'

  exception Error of string

  local
    structure M = MetaSyn
    structure I = IntSyn

    fun subgoal (M.State (name, M.Prefix (G, M, B), V)) =
        let
          fun (* GEN BEGIN FUN FIRST *) check I.Null = true (* GEN END FUN FIRST *)
            | (* GEN BEGIN FUN BRANCH *) check (I.Decl (M, M.Top)) = check M (* GEN END FUN BRANCH *)
            | (* GEN BEGIN FUN BRANCH *) check (I.Decl (M, M.Bot)) = false (* GEN END FUN BRANCH *)
        in
          check M
        end

  in
    (* GEN BEGIN TAG OUTSIDE LET *) val subgoal = subgoal (* GEN END TAG OUTSIDE LET *)
  end (* local *)
end (* GEN END FUNCTOR DECL *); (* functor Qed *)
