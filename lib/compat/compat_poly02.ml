(* Compatibility shim from Basis-current to Poly/ML of 4.1.3 *)

(* Author: Christopher Richards *)

module Compat : Compat.COMPAT =
  Compat
    (struct
      module Array = CompatArray97
    end)
    (struct
      module Vector = CompatVector97
    end)
    (struct
      module Path = OSPath
    end)
    (struct
      module Substring = CompatSubstring97
    end)
    (struct
      module TextIO = CompatTextIO97
    end)
    (struct
      module Timer = Timer
    end)
