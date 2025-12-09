module SwMemoTable ((* (TableParam : TABLEPARAM) *)
                     (MemoTable : MEMOTABLE)
                     (MemoTableInst : MEMOTABLE): MEMOTABLE =
                     (*! sharing MemoTableInst.IntSyn = MemoTable.IntSyn !*)
                     (*! sharing MemoTableInst.CompSyn = MemoTable.CompSyn !*)
                     (*! sharing MemoTableInst.TableParam = MemoTable.TableParam !*)
struct

  (*! module IntSyn = MemoTable.IntSyn !*)
  (*! module CompSyn = MemoTable.CompSyn !*)
  (*! module TableParam = MemoTable.TableParam !*)


  let rec callCheck args =
    case (!TableParam.strategy)
      of TableParam.Variant => MemoTable.callCheck args
    | TableParam.Subsumption => MemoTableInst.callCheck args


  let rec insertIntoTree args =
    case (!TableParam.strategy)
      of TableParam.Variant => MemoTable.insertIntoTree args
    | TableParam.Subsumption => MemoTableInst.insertIntoTree args

  let rec answerCheck args =
    case (!TableParam.strategy)
      of TableParam.Variant => MemoTable.answerCheck args
    | TableParam.Subsumption => MemoTableInst.answerCheck args


  let rec reset () =
    case (!TableParam.strategy)
      of TableParam.Variant => MemoTable.reset ()
    | TableParam.Subsumption => MemoTableInst.reset ()

  let rec updateTable () =
    case (!TableParam.strategy)
      of TableParam.Variant => MemoTable.updateTable ()
    | TableParam.Subsumption => MemoTableInst.updateTable ()

  let rec tableSize () =
    case (!TableParam.strategy)
      of TableParam.Variant => MemoTable.tableSize ()
    | TableParam.Subsumption => MemoTableInst.tableSize ()


  let rec memberCtx args =
    case (!TableParam.strategy) of
      TableParam.Subsumption => MemoTableInst.memberCtx args
    | TableParam.Variant => MemoTable.memberCtx args

end;; (* functor SwMemoTable *)

