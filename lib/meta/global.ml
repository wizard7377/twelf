(* Meta Global parameters *)
(* Author: Carsten Schuermann *)

let recctor MTPGlobal
  (module MetaGlobal : METAGLOBAL): MTPGLOBAL =
struct
  type ProverType = New | Old

  let prover = ref New
  let maxFill = MetaGlobal.maxFill
  let maxSplit = MetaGlobal.maxSplit
  let maxRecurse = MetaGlobal.maxRecurse
end; (* module MTPGlobal *)
