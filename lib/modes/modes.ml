open Basis ;; 
(* structure ModeSyn  in modesyn.sml *)

module ModeTable = ModeTable (struct
  module Table = IntRedBlackTree
end)

module ModeDec = ModeDec

module ModeCheck =
  ModeCheck
    (struct
      module ModeTable = ModeTable
    end)
    (struct
      module Whnf = Whnf
    end)
    (struct
      module Index = Index
    end)
    (struct
      module Origins = Origins
    end)

module ModePrint =
  ModePrint
    (struct
      module Names = Names
    end)
    (struct
      module Formatter = Formatter
    end)
    (struct
      module Print = Print
    end)
