(* Indexing *)

(* Author: Brigitte Pientka *)

module type MEMOTABLE = sig
  (*! structure IntSyn : INTSYN !*)
  (*! structure CompSyn : COMPSYN !*)
  (*! structure TableParam : TABLEPARAM !*)
  (* call check/insert *)
  (* callCheck (G, D, U, eqn)
   *
   * if D, G |- U & eqn     in table  then RepeatedEntry (entries)
   * if D, G |- U & eqn not in table  then NewEntry (ptrAnswer)
   * SIDE EFFECT: D, G |- U added to table
   *)
  val callCheck :
    IntSyn.dctx
    * IntSyn.dctx
    * IntSyn.dctx
    * IntSyn.exp
    * TableParam.resEqn
    * TableParam.status ->
    TableParam.callCheckResult

  val insertIntoTree :
    IntSyn.dctx
    * IntSyn.dctx
    * IntSyn.dctx
    * IntSyn.exp
    * TableParam.resEqn
    * TableParam.answer
    * TableParam.status ->
    TableParam.callCheckResult

  (* answer check/insert *)
  (* answerCheck (G, D, (U,s))
   * 
   * Assupmtion: D, G |- U is in table
   *             and A represents the corresponding solutions
   * 
   * G |- s : D, G
   * Dk, G |- sk : D, G
   *
   * If  (Dk, sk) in A then repeated
   *  else new
   *)
  val answerCheck :
    IntSyn.sub * TableParam.answer * CompSyn.pskeleton -> TableParam.answState

  (* reset table *)
  val reset : unit -> unit

  (* updateTable 
   *
   * SIDE EFFECT: 
   *   for_sml each table entry: 
   *       advance lookup pointer
   *
   * if Table did not change during last stage 
   *    then updateTable () =  false
   * else updateTable () = true
   *)
  val updateTable : unit -> bool
  val tableSize : unit -> int
  val memberCtx : (IntSyn.dctx * IntSyn.exp) * IntSyn.dctx -> IntSyn.dec option
end

(* signature MemoTable *)
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
