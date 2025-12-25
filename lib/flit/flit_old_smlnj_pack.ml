open Basis ;; 
(* cope with nonstandard old smlnj name of PackWord32Little -jcreed 2006.9.15 *)

module Flit =
  Flit
    (struct
      module Global = Global
    end)
    (struct
      module Word = Word32
    end)
    (struct
      module Pack = Pack32Little
    end)
    (struct
      module IntSyn = IntSyn
    end)
    (struct
      module Whnf = Whnf
    end)
    (struct
      module Print = Print
    end)
    (struct
      module Names = Names
    end)
    (struct
      module Index = Index
    end)
    (struct
      module Table = IntRedBlackTree
    end)
