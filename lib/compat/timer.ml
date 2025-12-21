(* Compatibility shim from Basis-current Timer to Basis-97 Timer *)

(* Author: Christopher Richards *)

module CompatTimer97 : COMPAT_TIMER = struct
  let rec checkCPUTimer timer =
    let { usr; sys; gc } = Timer.checkCPUTimer timer in
    { usr; sys }

  let rec checkGCTime timer =
    let { gc; _ } = Timer.checkCPUTimer timer in
    gc
end
