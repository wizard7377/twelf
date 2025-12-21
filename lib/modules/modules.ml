module ModSyn =
  ModSyn
    (struct
      module Global = Global
    end)
    (struct
      module Names' = Names
    end)
    (struct
      module Origins = Origins
    end)
    (struct
      module Whnf = Whnf
    end)
    (struct
      module Strict = Strict
    end)
    (struct
      module IntTree = IntRedBlackTree
    end)
    (struct
      module HashTable = StringHashTable
    end)
