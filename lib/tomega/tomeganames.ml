(* Naming *)

(* Author: Carsten Schuermann *)

module TomegaNames : TOMEGANAMES = struct
  module T = Tomega
  module I = IntSyn

  let rec decName = function
    | Psi, T.UDec D -> T.UDec (Names.decName (T.coerceCtx Psi, D))
    | Psi, T.PDec (x, F, TC1, TC2) ->
        let (I.NDec x') = Names.decName (T.coerceCtx Psi, I.NDec x) in
        T.PDec (x', F, TC1, TC2)
end
