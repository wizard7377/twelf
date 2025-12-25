open Basis ;; 

module Checking =
  Checking
    (struct
      module Global = Global
    end)
    (struct
      module Whnf = Whnf
    end)
    (struct
      module Conv = Conv
    end)
    (struct
      module Unify = UnifyTrail
    end)
    (struct
      module Trail = Trail
    end)
    (struct
      module Names = Names
    end)
    (struct
      module Index = Index
    end)
    (struct
      module Subordinate = Subordinate
    end)
    (struct
      module Formatter = Formatter
    end)
    (struct
      module Print = Print
    end)
    (struct
      module Order = Order
    end)
    (struct
      module Paths = Paths
    end)
    (struct
      module Origins = Origins
    end)

module Reduces =
  Reduces
    (struct
      module Global = Global
    end)
    (struct
      module Whnf = Whnf
    end)
    (struct
      module Names = Names
    end)
    (struct
      module Index = Index
    end)
    (struct
      module Subordinate = Subordinate
    end)
    (struct
      module Formatter = Formatter
    end)
    (struct
      module Print = Print
    end)
    (struct
      module Order = Order
    end)
    (struct
      module Checking = Checking
    end)
    (struct
      module Paths = Paths
    end)
    (struct
      module Origins = Origins
    end)
