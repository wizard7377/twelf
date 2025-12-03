(* Naming *)
(* Author: Carsten Schuermann *)

module TomegaNames : TOMEGANAMES=
  struct
    module T = Tomega
    module I = IntSyn

    fun decName (Psi, T.UDec D) = T.UDec (Names.decName (T.coerceCtx Psi, D))
      | decName (Psi, T.PDec (x, F, TC1, TC2)) =
        let
          let I.NDec x' =  Names.decName (T.coerceCtx Psi, I.NDec x)
        in
          T.PDec (x', F, TC1, TC2)
        end
  end