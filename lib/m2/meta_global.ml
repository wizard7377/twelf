(* Global parameters *)
(* Author: Carsten Schuermann *)

(MetaGlobal : METAGLOBAL) =
struct
  type strategy = RFS | FRS

  let strategy = ref FRS
  let maxFill = ref 6
  let maxSplit = ref 2
  let maxRecurse = ref 10
end;; (* module MetaGlobal *)
