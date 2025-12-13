(* Naming *)
(* Author: Carsten Schuermann *)

structure TomegaNames : TOMEGANAMES=
  struct
    structure T = Tomega
    structure I = IntSyn

    fun (* GEN BEGIN CASE FIRST *) (* GEN BEGIN CASE FIRST *) decName (Psi, T.UDec D) = T.UDec (Names.decName (T.coerceCtx Psi, D)) (* GEN END CASE FIRST *) (* GEN END CASE FIRST *)
      | (* GEN BEGIN CASE BRANCH *) (* GEN BEGIN CASE BRANCH *) decName (Psi, T.PDec (x, F, TC1, TC2)) =
        let
          val I.NDec x' =  Names.decName (T.coerceCtx Psi, I.NDec x)
        in
          T.PDec (x', F, TC1, TC2)
        end (* GEN END CASE BRANCH *) (* GEN END CASE BRANCH *)
  end