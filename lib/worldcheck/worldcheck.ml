module MemoTable = HashTable


module WorldSyn = WorldSyn (struct module Global = Global end) (struct module Whnf = Whnf end) (struct module Names = Names end) (struct module Unify = UnifyTrail end) (struct module Abstract = Abstract end) (struct module Constraints = Constraints end) (struct module Index = Index end) (struct module Subordinate = Subordinate end) (struct module Print = Print end) (struct module Table = IntRedBlackTree end) (struct module Paths = Paths end) (struct module Origins = Origins end) (struct module Timers = Timers end)


module Worldify = Worldify (struct module Global = Global end) (struct module WorldSyn = WorldSyn end) (struct module Whnf = Whnf end) (struct module Names = Names end) (struct module Unify = UnifyTrail end) (struct module Abstract = Abstract end) (struct module Constraints = Constraints end) (struct module Index = Index end) (struct module CSManager = CSManager end) (struct module Subordinate = Subordinate end) (struct module Print = Print end) (struct module Table = IntRedBlackTree end) (struct module MemoTable = MemoTable end) (struct module IntSet = IntSet end) (struct module Origins = Origins end)

