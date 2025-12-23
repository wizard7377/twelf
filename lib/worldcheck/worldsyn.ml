(* World Checking *)

(* Author: Carsten Schuermann *)

module type WORLDSYN = sig
  exception Error of string

  val reset : unit -> unit
  val install : IntSyn.cid * Tomega.worlds -> unit
  val lookup : IntSyn.cid -> Tomega.worlds

  (* raises Error if undeclared *)
  val uninstall : IntSyn.cid -> bool

  (* true if declared *)
  val worldcheck : Tomega.worlds -> IntSyn.cid -> unit
  val ctxToList : IntSyn.dec IntSyn.ctx -> IntSyn.dec list
  val isSubsumed : Tomega.worlds -> IntSyn.cid -> unit
  val getWorlds : IntSyn.cid -> Tomega.worlds
end

(* signature WORLDSYN *)
(* World Checking *)

(* Author: Carsten Schuermann *)

(* Modified: Frank Pfenning *)

module WorldSyn
    (Global : Global.GLOBAL)
    (Whnf : Whnf.WHNF)
    (Index : Index.INDEX)
    (Names : Names.NAMES)
    (Unify : Unify.UNIFY)
    (Abstract : Abstract.ABSTRACT)
    (Constraints : Constraints.CONSTRAINTS)
    (Subordinate : Subordinate.SUBORDINATE)
    (Print : Print.PRINT)
    (Origins : Origins.ORIGINS)
    (Timers : Timers.TIMERS) : WORLDSYN = struct
  module I = IntSyn
  module T = Tomega
  module P = Paths
  module F = PrintFormatter

  exception Error of string
  exception Error' of P.occ * string
  (* copied from terminates/reduces.fun *)

  let rec wrapMsg (c, occ, msg) =
    match Origins.originLookup c with
    | fileName, None -> fileName ^ ":" ^ msg
    | fileName, Some occDec ->
        P.wrapLoc'
          ( P.Loc (fileName, P.occToRegionDec occDec occ),
            Origins.linesInfoLookup fileName,
            "While checking constant "
            ^ Names.qidToString (Names.constQid c)
            ^ ":\n" ^ msg )

  type dlist = IntSyn.dec list

  let worldsTable : T.worlds Table.table = Table.new_ 0
  let rec reset () = Table.clear worldsTable
  let rec insert (cid, W) = Table.insert worldsTable (cid, W)

  let rec getWorlds b =
    match Table.lookup worldsTable b with
    | None ->
        raise
          (Error
             ("Family "
             ^ Names.qidToString (Names.constQid b)
             ^ " has no worlds declaration"))
    | Some Wb -> Wb
  (* subsumedTable
       For each family a that is world-checked, this
       contains the subordinate families b whose worlds
       subsume that of a modulo subordination
    *)

  let subsumedTable : unit Table.table = Table.new_ 0
  let rec subsumedReset () = Table.clear subsumedTable
  let rec subsumedInsert cid = Table.insert subsumedTable (cid, ())

  let rec subsumedLookup cid =
    match Table.lookup subsumedTable cid with None -> false | Some _ -> true
  (* Regular world expressions R
       Invariants:
       If R = (D1,...,Dn)[s] then G |- s : G' and G' |- D1,...,Dn ctx
       If R = r* then r = 1 or r does not accept the empty world
    *)

  type reg =
    | Block of I.dctx * dlist
    | Seq of dlist * I.sub
    | Star of reg
    | Plus of reg * reg
    | One
  (*     | 1                    *)

  exception Success
  (* signals worldcheck success *)

  (* Format a regular world *)

  let rec formatReg r =
    match r with
    | Block (G, dl) -> Print.formatDecList (G, dl) (* Is this correct? - gaw *)
    (* Fixed June 3, 2009 -fp,cs *)
    | Seq (dl, s) -> Print.formatDecList' (I.Null, (dl, s))
    | Star r -> F.Hbox [ F.String "("; formatReg r; F.String ")*" ]
    | Plus (r1, r2) ->
        F.HVbox
          [
            F.String "(";
            formatReg r1;
            F.String ")";
            F.Break;
            F.String "|";
            F.Space;
            F.String "(";
            formatReg r2;
            F.String ")";
          ]
    | One -> F.String "1"
  (* Format a subsumption failure judgment
       msg: Prefix for_sml the message
       dl : declaration list
       Rb : regular world
       b : family
       Displays:

         msg for_sml family b:
         G |- dl </: Rb
     *)

  let rec formatSubsump msg (G, dl, Rb, b) =
    (*
            F.HVbox ([F.String ((Names.qidToString (Names.constQid b)) ^ ":")])
        *)
    F.HVbox
      [
        F.String msg;
        F.Space;
        F.String "for_sml family";
        F.Space;
        F.String (Names.qidToString (Names.constQid b) ^ ":");
        F.Break;
        (* F.Newline (), *)
        (* Do not print some-variables; reenable if necessary *)
        (* June 3, 2009 -fp,cs *)
        (* Print.formatCtx(I.Null, G), F.Break, F.String "|-", F.Space, *)
        Print.formatDecList (G, dl);
        F.Break;
        F.String "</:";
        F.Space;
        formatReg Rb;
      ]
  (* createEVarSub G G' = s

       Invariant:
       If   G is a context
       and  G' is a context
       then G |- s : G'
    *)

  let rec createEVarSub = function
    | G, I.Null -> I.Shift (I.ctxLength G)
    | G, I.Decl (G', D) ->
        let s = createEVarSub (G, G') in
        let V' = I.EClo (V, s) in
        let X = I.newEVar (G, V') in
        I.Dot (I.Exp X, s)
  (* from cover.fun *)

  (* collectConstraints (Xs) = constrs
       collect all the constraints that may be attached to EVars in Xs

       try simplifying away the constraints in case they are "hard"
    *)

  let rec collectConstraints = function
    | [] -> []
    | I.EVar (_, _, _, { contents = [] }) :: Xs -> collectConstraints Xs
    | I.EVar (_, _, _, { contents = constrs }) :: Xs ->
        Constraints.simplify constrs @ collectConstraints Xs
  (* collectEVars (G, s, Xs) = Xs'
       adds all uninstantiated EVars from s to Xs to obtain Xs'
       Invariant: s is EVar substitutions
    *)

  let rec collectEVars = function
    | G, I.Dot (I.Exp X, s), Xs ->
        collectEVars (G, s, Abstract.collectEVars (G, (X, I.id), Xs))
    | G, I.Shift _, Xs -> Xs
  (* other cases impossible by invariants since s is EVarSubst *)

  (* noConstraints (G, s) = true iff there are no remaining constraints in s
       Invariants: s is an EVar substitution X1...Xn.^k
    *)

  let rec noConstraints (G, s) =
    match collectConstraints (collectEVars (G, s, [])) with
    | [] -> true
    | _ -> false
  (* end from cover.fun *)

  (************)

  (* Printing *)

  (************)

  (* Declarations *)

  let rec formatD (G, D) =
    F.Hbox [ F.String "{"; Print.formatDec (G, D); F.String "}" ]
  (* Declaration lists *)

  let rec formatDList = function
    | G, [], t -> []
    | G, D :: [], t ->
        let D' = I.decSub (D, t) in
        formatD (G, D') :: [] (* Names.decUName (G, I.decSub(D, t)) *)
    | G, D :: L, t ->
        (* Names.decUName (G, I.decSub (D, t)) *)
        let D' = I.decSub (D, t) in
        formatD (G, D') :: F.Break :: formatDList (I.Decl (G, D'), L, I.dot1 t)
  (*
    fun hypsToDList (I.Root _) = nil
      | hypsToDList (I.Pi ((D, _), V)) =
          D::hypsToDList V
    *)

  (* Hypotheses and declaration lists *)

  let rec wGoalToString ((G, L), Seq (piDecs, t)) =
    F.makestring_fmt
      (F.HVbox
         [
           F.HVbox (formatDList (G, L, I.id));
           F.Break;
           F.String "<|";
           F.Break;
           F.HVbox (formatDList (G, piDecs, t));
         ])
  (* Declaration list *)

  let rec worldToString (G, Seq (piDecs, t)) =
    F.makestring_fmt (F.HVbox (formatDList (G, piDecs, t)))
  (* Hypotheses *)

  let rec hypsToString (G, L) =
    F.makestring_fmt (F.HVbox (formatDList (G, L, I.id)))
  (* Mismatch between hypothesis and world declaration *)

  let rec mismatchToString (G, (V1, s1), (V2, s2)) =
    F.makestring_fmt
      (F.HVbox
         [
           Print.formatExp (G, I.EClo (V1, s1));
           F.Break;
           F.String "<>";
           F.Break;
           Print.formatExp (G, I.EClo (V2, s2));
         ])
  (***********)

  (* Tracing *)

  (***********)

  module Trace : sig
    val clause : I.cid -> unit
    val constraintsRemain : unit -> unit
    val matchBlock : (I.dctx * dlist) * reg -> unit
    val unmatched : I.dctx * dlist -> unit
    val missing : I.dctx * reg -> unit
    val mismatch : I.dctx * I.eclo * I.eclo -> unit
    val success : unit -> unit
  end = struct
    let rec clause c =
      print
        ("World checking clause " ^ Names.qidToString (Names.constQid c) ^ "\n")

    let rec constraintsRemain () =
      if !Global.chatter > 7 then
        print
          "Constraints remain after matching hypotheses against context block\n"
      else ()

    let rec matchBlock (GL, R) =
      (* R = (D1,...,Dn)[t] *)
      if !Global.chatter > 7 then
        print ("Matching:\n" ^ wGoalToString (GL, R) ^ "\n")
      else ()

    let rec unmatched GL =
      if !Global.chatter > 7 then
        print ("Unmatched hypotheses:\n" ^ hypsToString GL ^ "\n")
      else ()

    let rec missing (G, R) =
      (* R = (D1,...,Dn)[t] *)
      if !Global.chatter > 7 then
        print ("Missing hypotheses:\n" ^ worldToString (G, R) ^ "\n")
      else ()

    let rec mismatch (G, Vs1, Vs2) =
      if !Global.chatter > 7 then
        print ("Mismatch:\n" ^ mismatchToString (G, Vs1, Vs2) ^ "\n")
      else ()

    let rec success () = if !Global.chatter > 7 then print "Success\n" else ()
  end

  let rec decUName (G, D) = I.Decl (G, Names.decUName (G, D))
  let rec decEName (G, D) = I.Decl (G, Names.decEName (G, D))
  (**************************************)

  (* Matching hypotheses against worlds *)

  (**************************************)

  let rec subGoalToDList = function
    | I.Pi ((D, _), V) -> D :: subGoalToDList V
    | I.Root _ -> []
  (* worldsToReg (Worlds [c1,...,cn]) = R
       W = R, except that R is a regular expression
       with non-empty leaves
    *)

  let rec worldsToReg = function
    | T.Worlds [] -> One
    | T.Worlds cids -> Star (worldsToReg' cids)

  and worldsToReg' = function
    | cid :: [] -> Block (I.constBlock cid)
    | cid :: cids -> Plus (Block (I.constBlock cid), worldsToReg' cids)
  (* init b (G, L) raises Success iff V is empty
       or none of the remaining declarations are relevant to b
       otherwise fails by returning ()
       Initial continuation for_sml world checker

       Invariant: G |- L dlist, L nf
    *)

  let rec init = function
    | b, (_, []) ->
        Trace.success ();
        raise Success
    | b, (G, L) ->
        if Subordinate.belowEq (I.targetFam V1, b) then (
          Trace.unmatched (G, L);
          ())
        else init b (decUName (G, D1), L2)
  (* accR ((G, L), R, k)   raises Success
       iff L = L1,L2 such that R accepts L1
           and k ((G, L1), L2) succeeds
       otherwise fails by returning ()
       Invariant: G |- L dlist, L nf
                  R regular world expression
       trails at choice points to undo EVar instantiations during matching
    *)

  let rec accR = function
    | GL, One, b, k -> k GL
    | GL, Block (someDecs, piDecs), b, k ->
        (* G |- t : someDecs *)
        (* if block matches, check for_sml remaining constraints *)
        let t = createEVarSub (G, someDecs) in
        let _ = Trace.matchBlock (GL, Seq (piDecs, t)) in
        let k' =
         fun GL' ->
          if noConstraints (G, t) then k GL'
          else (
            Trace.constraintsRemain ();
            ())
        in
        accR (GL, Seq (piDecs, t), b, k')
    | (G, L), L', b, k ->
        if Unify.unifiable (G, (V1, I.id), (V1', t)) then
          accR ((decUName (G, D), L2), Seq (L2', I.dot1 t), b, k)
        else if Subordinate.belowEq (I.targetFam V1, b) then (
          (* relevant to family b, fail *)
          Trace.mismatch (G, (V1, I.id), (V1', t));
          ())
        else (* not relevant to family b, skip in L *)
          accR ((decUName (G, D), L2), Seq (B', I.comp (t, I.shift)), b, k)
    | GL, Seq ([], t), b, k -> k GL
    | GL, R, b, k ->
        Trace.missing (G, R);
        ()
    | GL, Plus (r1, r2), b, k ->
        Cs.CSManager.trail (fun () -> accR (GL, r1, b, k));
        accR (GL, r2, b, k)
    | GL, Star One, b, k -> k GL
    | GL, r, b, k ->
        Cs.CSManager.trail (fun () -> k GL);
        accR (GL, r', b, fun GL' -> accR (GL', r, b, k))
  (* checkSubsumedBlock (G, someDecs, piDecs, Rb, b) = ()
       iff block SOME someDecs. PI piDecs is subsumed by Rb
       Effect: raises Error (msg) otherwise

       Invariants: Rb = reg (worlds (b))
    *)

  let rec checkSubsumedBlock (G, L', Rb, b) =
    try
      accR ((G, L'), Rb, b, init b);
      raise
        (Error
           (F.makestring_fmt
              (formatSubsump "World subsumption failure" (G, L', Rb, b))))
    with Success -> ()
  (* checkSubsumedWorlds (Wa, Rb, b) = ()
       iff Wa is subsumed by Rb
       Effect: raises Error (msg) otherwise

       Invariants: Rb = reg (worlds (b))
    *)

  let rec checkSubsumedWorlds = function
    | [], Rb, b -> ()
    | cid :: cids, Rb, b ->
        let someDecs, piDecs = I.constBlock cid in
        checkSubsumedBlock (Names.ctxName someDecs, piDecs, Rb, b);
        checkSubsumedWorlds (cids, Rb, b)
  (* checkBlocks W (G, V, occ) = ()
       iff V = {{G'}} a @ S and G' satisfies worlds W
       Effect: raises Error'(occ, msg) otherwise

       Invariants: G |- V : type, V nf
    *)

  let rec checkBlocks (T.Worlds cids) (G, V, occ) =
    try
      let b = I.targetFam V in
      let Wb = try getWorlds b with Error msg -> raise (Error' (occ, msg)) in
      let Rb = worldsToReg Wb in
      let _ =
        if subsumedLookup b then ()
        else
          try
            checkSubsumedWorlds (cids, Rb, b);
            subsumedInsert b
          with Error msg -> raise (Error' (occ, msg))
      in
      let L = subGoalToDList V in
      accR ((G, L), Rb, b, init b);
      raise
        (Error'
           ( occ,
             F.makestring_fmt (formatSubsump "World violation" (G, L, Rb, b)) ))
    with Success -> ()
  (******************************)

  (* Checking clauses and goals *)

  (******************************)

  (* checkClause (G, V, W, occ) = ()
       iff all subgoals in V satisfy world spec W
       Effect: raises Error' (occ', msg) otherwise

       Invariant: G |- V : type, V nf
       occ is occurrence of V in current clause
     *)

  let rec checkClause = function
    | G, I.Root (a, S), W, occ -> ()
    | G, I.Pi ((D, I.Maybe), V2), W, occ ->
        checkClause (decEName (G, D), V2, W, P.body occ);
        checkGoal (G, V1, W, P.label occ)
    | G, I.Pi ((D, I.No), V2), W, occ ->
        checkBlocks W (G, V1, P.label occ);
        checkClause (decEName (G, D), V2, W, P.body occ);
        checkGoal (G, V1, W, P.label occ)

  and checkGoal = function
    | G, I.Root (a, S), W, occ -> ()
    | G, I.Pi ((D, _), V2), W, occ ->
        checkGoal (decUName (G, D), V2, W, P.body occ);
        checkClause (G, V1, W, P.label occ)
  (* worldcheck W a = ()
       iff all subgoals in all clauses defining a satisfy world spec W
       Effect: raises Error(msg) otherwise, where msg includes location
    *)

  let rec worldcheck W a =
    (* initialize table of subsumed families *)
    let _ =
      if !Global.chatter > 3 then
        print
          ("World checking family "
          ^ Names.qidToString (Names.constQid a)
          ^ ":\n")
      else ()
    in
    let _ = subsumedReset () in
    let rec checkAll = function
      | [] -> ()
      | I.Const c :: clist -> (
          if !Global.chatter = 4 then
            print (Names.qidToString (Names.constQid c) ^ " ")
          else ();
          if !Global.chatter > 4 then Trace.clause c else ();
          try checkClause (I.Null, I.constType c, W, P.top)
          with Error' (occ, msg) ->
            raise (Error (wrapMsg (c, occ, msg)));
            checkAll clist)
      | I.Def d :: clist -> (
          if !Global.chatter = 4 then
            print (Names.qidToString (Names.constQid d) ^ " ")
          else ();
          if !Global.chatter > 4 then Trace.clause d else ();
          try checkClause (I.Null, I.constType d, W, P.top)
          with Error' (occ, msg) ->
            raise (Error (wrapMsg (d, occ, msg)));
            checkAll clist)
    in
    let _ = checkAll (Index.lookup a) in
    let _ = if !Global.chatter = 4 then print "\n" else () in
    ()
  (**************************)

  (* Checking Subordination *)

  (**************************)

  (*
       At present, worlds declarations must respect the
       current subordination relation in order to guarantee
       soundness.
    *)

  let rec ctxAppend = function
    | G, I.Null -> G
    | G, I.Decl (G', D) -> I.Decl (ctxAppend (G, G'), D)
  (* checkSubordBlock (G, G', L') = ()
       Effect: raises Error(msg) if subordination is not respected
               in context block SOME G'. PI L'
       Invariants: G |- SOME G'. PI L' block
    *)

  let rec checkSubordBlock (G, G', L) = checkSubordBlock' (ctxAppend (G, G'), L)

  and checkSubordBlock' = function
    | G, D :: L' ->
        Subordinate.respectsN (G, V);
        (* is V nf?  Assume here: yes! *)
        checkSubordBlock' (I.Decl (G, D), L')
    | G, [] -> ()
  (* conDecBlock (condec) = (Gsome, Lpi)
       if condec is a block declaration
       raise Error (msg) otherwise
    *)

  let rec conDecBlock = function
    | I.BlockDec (_, _, Gsome, Lpi) -> (Gsome, Lpi)
    | condec ->
        raise
          (Error ("Identifier " ^ I.conDecName condec ^ " is not a block label"))
  (* constBlock cid = (someDecs, piDecs)
       if cid is a context block
       Effect: raise Error (msg) otherwise
    *)

  let rec constBlock cid = conDecBlock (I.sgnLookup cid)
  (* checkSubordWorlds (W) = ()
       Effect: raises Error(msg) if subordination is not respected
               in some context block in W
    *)

  let rec checkSubordWorlds = function
    | [] -> ()
    | cid :: cids ->
        let someDecs, piDecs = constBlock cid in
        checkSubordBlock (I.Null, someDecs, piDecs);
        checkSubordWorlds cids
  (* install (a, W) = ()
       install worlds declaration W for_sml family a

       Effect: raises Error if W does not respect subordination
    *)

  let rec install (a, W) =
    try checkSubordWorlds cids
    with Subordinate.Error msg ->
      raise (Error msg);
      insert (a, W)

  let rec uninstall a =
    match Table.lookup worldsTable a with
    | None -> false
    | Some _ ->
        Table.delete worldsTable a;
        true
  (* lookup (a) = SOME W if worlds declared for_sml a, NONE otherwise *)

  let rec lookup a = getWorlds a
  (* ctxToList G = L

       Invariant:
       G = L  (G is left associative, L is right associative)
    *)

  let rec ctxToList Gin =
    let rec ctxToList' = function
      | I.Null, G -> G
      | I.Decl (G, D), G' -> ctxToList' (G, D :: G')
    in
    ctxToList' (Gin, [])
  (* isSubsumed (W, b) = ()
       holds if the worlds associated with b are subsumed by W
       Effect: raises Error'(occ, msg) otherwise

       Invariants: G |- V : type, V nf
    *)

  let rec isSubsumed (T.Worlds cids) b =
    let Wb = getWorlds b in
    let Rb = worldsToReg Wb in
    if subsumedLookup b then ()
    else (
      checkSubsumedWorlds (cids, Rb, b);
      subsumedInsert b)

  let reset = reset
  let install = install
  let lookup = lookup
  let uninstall = uninstall
  let worldcheck = worldcheck
  let ctxToList = ctxToList
  let isSubsumed = isSubsumed
  let getWorlds = getWorlds
end

(* functor WorldSyn *)
