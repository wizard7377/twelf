(* Naming *)
(* Author: Carsten Schuermann *)

structure TomegaNames : TOMEGANAMES=
  struct
    structure T = Tomega
    structure I = IntSyn

    fun (* GEN BEGIN FUN FIRST *) decName (Psi, T.UDec D) = T.UDec (Names.decName (T.coerceCtx Psi, D)) (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) decName (Psi, T.PDec (x, F, TC1, TC2)) =
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val I.NDec x' =  Names.decName (T.coerceCtx Psi, I.NDec x) (* GEN END TAG OUTSIDE LET *)
        in
          T.PDec (x', F, TC1, TC2)
        end (* GEN END FUN BRANCH *)
  end