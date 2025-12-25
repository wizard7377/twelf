open Basis ;; 
(* Total Declarations *)

(* Author: Frank Pfenning *)

module type TOTAL = sig
  (*! structure IntSyn : Intsyn.INTSYN !*)
  exception Error of string

  val reset : unit -> unit
  val install : IntSyn.cid -> unit

  (* install(a) --- a is total in its input arguments *)
  val uninstall : IntSyn.cid -> bool

  (* true: was known to be total *)
  val checkFam : IntSyn.cid -> unit
  (* may raise Error(msg) *)
end

(* signature TOTAL *)
(* Total Declarations *)

(* Author: Frank Pfenning *)

module Total
    (Global : Global.GLOBAL)
    (Whnf : Whnf.WHNF)
    (Names : Names.NAMES)
    (ModeTable : Modetable.MODETABLE)
    (ModeCheck : Modecheck.MODECHECK)
    (Index : Index.INDEX)
    (Subordinate : Subordinate.SUBORDINATE)
    (Order : Order.Order.ORDER)
    (Reduces : Reduces.REDUCES)
    (Cover : Cover.COVER)
    (Origins : Origins.ORIGINS)
    (Timers : Timers.TIMERS) : TOTAL = struct
  (*! structure IntSyn = IntSyn' !*)

  exception Error of string

  module I = IntSyn
  module P = Paths
  module M = ModeSyn
  module N = Names
  (* totalTable (a) = SOME() iff a is total, otherwise NONE *)

  let totalTable : unit Table.table = Table.new_ 0
  let rec reset () = Table.clear totalTable
  let rec install cid = Table.insert totalTable (cid, ())
  let rec lookup cid = Table.lookup totalTable cid
  let rec uninstall cid = Table.delete totalTable cid
  let reset = reset
  let install = install

  let uninstall =
   fun cid ->
    match lookup cid with
    | None -> false
    | Some _ ->
        uninstall cid;
        true

  let rec total cid =
    (* call only on constants *)
    match lookup cid with
    | None -> false
    | Some _ -> true

  exception Error' of P.occ * string
  (* copied from terminates/reduces.fun *)

  let rec error (c, occ, msg) =
    match Origins.originLookup c with
    | fileName, None -> raise (Error (fileName ^ ":" ^ msg))
    | fileName, Some occDec ->
        raise
          (Error
             (P.wrapLoc'
                ( P.Loc (fileName, P.occToRegionDec occDec occ),
                  Origins.linesInfoLookup fileName,
                  msg )))
  (* G is unused here *)

  let rec checkDynOrder = function
    | G, Vs, 0, occ ->
        if !Global.chatter >= 5 then
          print
            "Output coverage: skipping redundant checking of third-order clause\n"
        else ();
        ()
    | G, Vs, n, occ -> checkDynOrderW (G, Whnf.whnf Vs, n, occ)

  and checkDynOrderW = function
    | G, (I.Root _, s), n, occ -> ()
    | G, (I.Pi ((D1, I.No), V2), s), n, occ ->
        checkDynOrder (G, (V1, s), n - 1, P.label occ);
        checkDynOrder (I.Decl (G, D1), (V2, I.dot1 s), n, P.body occ)
    | G, (I.Pi ((D1, I.Maybe), V2), s), n, occ ->
        checkDynOrder (I.Decl (G, D1), (V2, I.dot1 s), n, P.body occ)
  (* checkClause (G, (V, s), occ) = ()
       checkGoal (G, (V, s), occ) = ()
       iff local output coverage for_sml V is satisfied
           for_sml clause V[s] or goal V[s], respectively.
       Effect: raises Error' (occ, msg) if coverage is not satisfied at occ.

       Invariants: G |- V[s] : type
    *)

  let rec checkClause (G, Vs, occ) = checkClauseW (G, Whnf.whnf Vs, occ)

  and checkClauseW = function
    | G, (I.Pi ((D1, I.Maybe), V2), s), occ ->
        let D1' = N.decEName (G, I.decSub (D1, s)) in
        checkClause (I.Decl (G, D1'), (V2, I.dot1 s), P.body occ)
    | G, (I.Pi ((D1, I.No), V2), s), occ ->
        let _ = checkClause (I.Decl (G, D1), (V2, I.dot1 s), P.body occ) in
        checkGoal (G, (V1, s), P.label occ)
    | G, (I.Root _, s), occ -> ()

  and checkGoal (G, Vs, occ) = checkGoalW (G, Whnf.whnf Vs, occ)

  and checkGoalW (G, (V, s), occ) =
    (* can raise Cover.Error for_sml third-order clauses *)
    let a = I.targetFam V in
    let _ =
      if not (total a) then
        raise
          (Error'
             ( occ,
               "Subgoal "
               ^ N.qidToString (N.constQid a)
               ^ " not declared to be total" ))
      else ()
    in
    let _ = checkDynOrderW (G, (V, s), 2, occ) in
    try Cover.checkOut (G, (V, s))
    with Cover.Error msg ->
      raise (Error' (occ, "Totality: Output of subgoal not covered\n" ^ msg))
  (* checkDefinite (a, ms) = ()
       iff every mode in mode spine ms is either input or output
       Effect: raises Error (msg) otherwise
    *)

  let rec checkDefinite = function
    | a, M.Mnil -> ()
    | a, M.Mapp (M.Marg (M.Plus, _), ms') -> checkDefinite (a, ms')
    | a, M.Mapp (M.Marg (M.Minus, _), ms') -> checkDefinite (a, ms')
    | a, M.Mapp (M.Marg (M.Star, xOpt), ms') ->
        error
          ( a,
            P.top,
            "Error: Totality checking "
            ^ N.qidToString (N.constQid a)
            ^ ":\n" ^ "All argument modes must be input (+) or output (-)"
            ^
            match xOpt with
            | None -> ""
            | Some x -> " but argument " ^ x ^ " is indefinite (*)" )
  (* checkOutCover [c1,...,cn] = ()
       iff local output coverage for_sml every subgoal in ci:Vi is satisfied.
       Effect: raises Error (msg) otherwise, where msg has filename and location.
    *)

  let rec checkOutCover = function
    | [] -> ()
    | I.Const c :: cs -> (
        if !Global.chatter >= 4 then print (N.qidToString (N.constQid c) ^ " ")
        else ();
        if !Global.chatter >= 6 then print "\n" else ();
        try checkClause (I.Null, (I.constType c, I.id), P.top)
        with Error' (occ, msg) ->
          error (c, occ, msg);
          checkOutCover cs)
    | I.Def d :: cs -> (
        if !Global.chatter >= 4 then print (N.qidToString (N.constQid d) ^ " ")
        else ();
        if !Global.chatter >= 6 then print "\n" else ();
        try checkClause (I.Null, (I.constType d, I.id), P.top)
        with Error' (occ, msg) ->
          error (d, occ, msg);
          checkOutCover cs)
  (* checkFam (a) = ()
       iff family a is total in its input arguments.
       This requires termination, input coverage, and local output coverage.
       Currently, there is no global output coverage.
       Effect: raises Error (msg) otherwise, where msg has filename and location.
    *)

  let rec checkFam a =
    (* Ensuring that there is no bad interaction with type-level definitions *)
    (* a cannot be a type-level definition *)
    (* Checking termination *)
    (* Checking input coverage *)
    (* by termination invariant, there must be consistent mode for_sml a *)
    (* must be defined and well-moded *)
    (* all arguments must be either input or output *)
    (* Checking output coverage *)
    (* all variables in output args must be free *)
    let _ = Cover.checkNoDef a in
    let _ =
      try
        Subordinate.checkNoDef a (* a cannot depend on type-level definitions *)
      with Subordinate.Error msg ->
        raise
          (Subordinate.Error
             ("Totality checking " ^ N.qidToString (N.constQid a) ^ ":\n" ^ msg))
    in
    let _ =
      try
        (Timers.time Timers.terminate Reduces.checkFam) a;
        if !Global.chatter >= 4 then
          print ("Terminates: " ^ N.qidToString (N.constQid a) ^ "\n")
        else ()
      with Reduces.Error msg -> raise (Reduces.Error msg)
    in
    let (Some ms) = ModeTable.modeLookup a in
    let _ = checkDefinite (a, ms) in
    let _ =
      try
        (Timers.time Timers.coverage Cover.checkCovers) (a, ms);
        if !Global.chatter >= 4 then
          print ("Covers (input): " ^ N.qidToString (N.constQid a) ^ "\n")
        else ()
      with Cover.Error msg -> raise (Cover.Error msg)
    in
    let _ =
      if !Global.chatter >= 4 then
        print
          ("Output coverage checking family "
          ^ N.qidToString (N.constQid a)
          ^ "\n")
      else ()
    in
    let _ = ModeCheck.checkFreeOut (a, ms) in
    let cs = Index.lookup a in
    let _ =
      try
        (Timers.time Timers.coverage checkOutCover) cs;
        if !Global.chatter = 4 then print "\n" else ();
        if !Global.chatter >= 4 then
          print ("Covers (output): " ^ N.qidToString (N.constQid a) ^ "\n")
        else ()
      with Cover.Error msg -> raise (Cover.Error msg)
    in
    ()
end

(* functor Total *)
