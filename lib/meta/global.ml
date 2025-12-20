(* Meta Global parameters *)


(* Author: Carsten Schuermann *)


module MTPGlobal (MetaGlobal : METAGLOBAL) : MTPGLOBAL = struct type proverType = New | Old
let prover = ref New
let maxFill = MetaGlobal.maxFill
let maxSplit = MetaGlobal.maxSplit
let maxRecurse = MetaGlobal.maxRecurse
 end


(* structure MTPGlobal *)

