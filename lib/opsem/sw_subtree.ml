module SwMemoTable (MemoTable : MEMOTABLE) (MemoTableInst : MEMOTABLE) :
  MEMOTABLE = struct
  (*! structure IntSyn = MemoTable.IntSyn !*)

  (*! structure CompSyn = MemoTable.CompSyn !*)

  (*! structure TableParam = MemoTable.TableParam !*)

  let rec callCheck args =
    match !TableParam.strategy with
    | TableParam.Variant -> MemoTable.callCheck args
    | TableParam.Subsumption -> MemoTableInst.callCheck args

  let rec insertIntoTree args =
    match !TableParam.strategy with
    | TableParam.Variant -> MemoTable.insertIntoTree args
    | TableParam.Subsumption -> MemoTableInst.insertIntoTree args

  let rec answerCheck args =
    match !TableParam.strategy with
    | TableParam.Variant -> MemoTable.answerCheck args
    | TableParam.Subsumption -> MemoTableInst.answerCheck args

  let rec reset () =
    match !TableParam.strategy with
    | TableParam.Variant -> MemoTable.reset ()
    | TableParam.Subsumption -> MemoTableInst.reset ()

  let rec updateTable () =
    match !TableParam.strategy with
    | TableParam.Variant -> MemoTable.updateTable ()
    | TableParam.Subsumption -> MemoTableInst.updateTable ()

  let rec tableSize () =
    match !TableParam.strategy with
    | TableParam.Variant -> MemoTable.tableSize ()
    | TableParam.Subsumption -> MemoTableInst.tableSize ()

  let rec memberCtx args =
    match !TableParam.strategy with
    | TableParam.Subsumption -> MemoTableInst.memberCtx args
    | TableParam.Variant -> MemoTable.memberCtx args
end

(* functor SwMemoTable *)
