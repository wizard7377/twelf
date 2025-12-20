module AbsMachine = AbsMachine (struct module Unify = UnifyTrail end) (struct module Assign = Assign end) (struct module Index = Index end) (struct module CPrint = CPrint end) (struct module Print = Print end) (struct module Names = Names end)


module AbstractTabled = AbstractTabled (struct module Print = Print end) (struct module Whnf = Whnf end) (struct module Unify = UnifyTrail end) (struct module Constraints = Constraints end) (struct module Subordinate = Subordinate end) (struct module Conv = Conv end) (struct module Print = Print end)


module MemoTable = MemoTable (struct module Conv = Conv end) (struct module Whnf = Whnf end) (struct module Print = Print end) (struct module AbstractTabled = AbstractTabled end) (struct module Table = IntRedBlackTree end)

module MemoTableInst = MemoTableInst (struct module Conv = Conv end) (struct module Whnf = Whnf end) (struct module Match = Match end) (struct module Assign = Assign end) (struct module Print = Print end) (struct module AbstractTabled = AbstractTabled end) (struct module Table = IntRedBlackTree end)

module SwMemoTable = SwMemoTable (struct module MemoTable = MemoTable end) (struct module MemoTableInst = MemoTableInst end)

module Tabled = Tabled (struct module Unify = UnifyTrail end) (struct module Match = Match end) (struct module TabledSyn = TabledSyn end) (struct module Assign = Assign end) (struct module Index = Index end) (struct module Queue = Queue end) (struct module MemoTable = SwMemoTable end) (struct module AbstractTabled = AbstractTabled end) (struct module CPrint = CPrint end) (struct module Print = Print end)


module PtRecon = PtRecon (struct module Unify = UnifyTrail end) (struct module MemoTable = SwMemoTable end) (struct module Assign = Assign end) (struct module Index = Index end) (struct module CPrint = CPrint end) (struct module Names = Names end)


module Trace = Trace (struct module Names = Names end) (struct module Whnf = Whnf end) (struct module Abstract = Abstract end) (struct module Print = Print end)


module AbsMachineSbt = AbsMachineSbt (struct module IntSyn' = IntSyn end) (struct module CompSyn' = CompSyn end) (struct module SubTree = SubTree end) (struct module Unify = UnifyTrail end) (struct module Assign = Assign end) (struct module Index = Index end) (struct module CPrint = CPrint end) (struct module Print = Print end) (struct module Names = Names end) (struct module CSManager = CSManager end)


module TMachine = TMachine (struct module Unify = UnifyTrail end) (struct module Index = Index end) (struct module Assign = Assign end) (struct module CPrint = CPrint end) (struct module Names = Names end) (struct module Trace = Trace end)


module SwMachine = SwMachine (struct module Trace = Trace end) (struct module AbsMachine = AbsMachine end) (struct module TMachine = TMachine end)

