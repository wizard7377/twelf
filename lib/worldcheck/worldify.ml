(* Worldify *)

(* Author: Carsten Schuermann *)

module type WORLDIFY = sig
  (*! structure IntSyn : Intsyn.INTSYN !*)
  (*! structure Tomega : Tomega.TOMEGA !*)
  exception Error of string

  val worldify : IntSyn.cid -> IntSyn.conDec list
  val worldifyGoal : IntSyn.dec IntSyn.ctx * IntSyn.exp -> IntSyn.exp
  (*  val check : Tomega.Worlds -> IntSyn.cid list -> unit
  val closure : Tomega.Worlds -> Tomega.Worlds *)
end

(* signature WORLDIFY *)
(* Worldification and World-checking *)

(* Author: Carsten Schuermann *)

(* Modified: Frank Pfenning *)

module Worldify
    (Global : Global.GLOBAL)
    (WorldSyn : Worldsyn.WORLDSYN)
    (Whnf : Whnf.WHNF)
    (Index : Index.INDEX)
    (Names : Names.NAMES)
    (Unify : Unify.UNIFY)
    (Abstract : Abstract.ABSTRACT)
    (Constraints : Constraints.CONSTRAINTS)
    (CSManager : Cs.Cs_manager.CS_MANAGER)
    (Subordinate : Subordinate.SUBORDINATE)
    (Print : Print.PRINT)
    (IntSet : Intset.INTSET)
    (Origins : Origins.ORIGINS) : WORLDIFY = struct
  (*! structure IntSyn = IntSyn !*)

  (*! structure Tomega = Tomega !*)

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
            "Constant " ^ Names.qidToString (Names.constQid c) ^ ":" ^ msg )

  let rec wrapMsgBlock (c, occ, msg) =
    match Origins.originLookup c with
    | fileName, None -> fileName ^ ":" ^ msg
    | fileName, Some occDec ->
        P.wrapLoc'
          ( P.Loc (fileName, P.occToRegionDec occDec occ),
            Origins.linesInfoLookup fileName,
            "Block " ^ Names.qidToString (Names.constQid c) ^ ":" ^ msg )

  type dlist = IntSyn.dec list

  module W = WorldSyn
  (* Regular world expressions R
       Invariants:
       If R = (D1,...,Dn)[s] then G |- s : G' and G' |- D1,...,Dn ctx
       If R = r* then r = 1 or r does not accept the empty world
    *)

  type reg =
    | Block of I.cid * (I.dctx * dlist)
    | Seq of int * dlist * I.sub
    | Star of reg
    | Plus of reg * reg
    | One
  (*     | 1                    *)

  exception Success of I.exp
  (* signals worldcheck success *)

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

  let rec wGoalToString ((G, L), Seq (_, piDecs, t)) =
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

  let rec worldToString (G, Seq (_, piDecs, t)) =
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
  (* ******************** *)

  (* World Subsumption    *)

  (* The STATIC part      *)

  (* ******************** *)

  (* equivList (G, (t, L), L')

        Invariant:
        If  . |- t : G
        and G |- L block
        then  B = true if  L [t] unifies with L'
              B = false otherwise
     *)

  let rec equivList = function
    | G, (_, []), [] -> true
    | G, (t, I.Dec (_, V1) :: L1), I.Dec (_, V2) :: L2 -> (
        try
          Unify.unify (G, (V1, t), (V2, I.id));
          equivList (G, (I.dot1 t, L1), L2)
        with Unify.Unify _ -> false)
    | _ -> false
  (* equivBlock ((G, L), L') = B

        Invariant:
        If   G |- L block
        then B = true if there exists a substitution . |- t : G, s.t. L[t] = L'
             B = false otherwise
     *)

  let rec equivBlock ((G, L), L') =
    let t = createEVarSub (I.Null, G) in
    equivList (I.Null, (t, L), L')
  (* equivBlocks W L = B

        Invariant:
        Let W be a world and L be a block.
        B = true if exists L' in W such that L = L'
        B = false otherwise
     *)

  let rec equivBlocks = function
    | W1, [] -> true
    | [], L' -> false
    | b :: W1, L' -> equivBlock (I.constBlock b, L') || equivBlocks W1 L'
  (* strengthen a (t, L) = L'

        Invariant:
        If   a is a type family,
        and  . |- t : G
        and  G |- L block
        then . |- L' block
        where V \in L and not V < a then V \in L'
        and   V \in L and V < a then not V \in L'
     *)

  let rec strengthen = function
    | a, (t, []) -> []
    | a, (t, D :: L) ->
        if Subordinate.below (I.targetFam V, a) then
          I.decSub (D, t) :: strengthen a (I.dot1 t, L)
        else strengthen a (I.Dot (I.Undef, t), L)
  (* subsumedBlock a W1 (G, L) = ()

        Invariant:
        If   a is a type family
        and  W1 the world in which the callee is defined
        and (G, L) one block in the world of the caller
        Then the function returns () if (G, L) is subsumed by W1
        otherwise Error is raised
     *)

  let rec subsumedBlock a W1 (G, L) =
    (* G |- t : someDecs *)
    let t = createEVarSub (I.Null, G) in
    let L' = strengthen a (t, L) in
    if equivBlocks W1 L' then ()
    else raise (Error "Static world subsumption failed")
  (* subsumedBlocks a W1 W2 = ()

        Invariant:
        Let W1 be the world in which the callee is defined
        Let W2 be the world in which the caller is defined
        Then the function returns () if W2 is subsumed by W1
        otherwise Error is raised
     *)

  let rec subsumedBlocks = function
    | a, W1, [] -> ()
    | a, W1, b :: W2 ->
        subsumedBlock a W1 (I.constBlock b);
        subsumedBlocks a W1 W2
  (* subsumedWorld a W1 W2 = ()

        Invariant:
        Let W1 be the world in which the callee is defined
        Let W2 be the world in which the caller is defined
        Then the function returns () if W2 is subsumed by W1
        otherwise Error is raised
     *)

  let rec subsumedWorld a (T.Worlds W1) (T.Worlds W2) = subsumedBlocks a W1 W2
  (* ******************** *)

  (* World Subsumption    *)

  (* The DYNAMIC part     *)

  (* ******************** *)

  (* eqCtx (G1, G2) = B

        Invariant:
        Let  G1, G2 constexts of declarations (as the occur in the some part
                    of a block).
        B = true if G1 and G2 are equal (modulo renaming of variables)
        B = false otherwise
     *)

  let rec eqCtx = function
    | I.Null, I.Null -> true
    | I.Decl (G1, D1), I.Decl (G2, D2) ->
        eqCtx (G1, G2) && Conv.convDec ((D1, I.id), (D2, I.id))
    | _ -> false
  (* eqList (L1, L2) = B

        Invariant:
        Let  L1, L2 lists of declarations (as the occur in a block).
        B = true if L1 and L2 are equal (modulo renaming of variables)
        B = false otherwise
     *)

  let rec eqList = function
    | [], [] -> true
    | D1 :: L1, D2 :: L2 ->
        Conv.convDec ((D1, I.id), (D2, I.id)) && eqList (L1, L2)
    | _ -> false
  (* eqBlock (b1, b2) = B

        Invariant:
        Let  b1, b2 blocks.
        B = true if b1 and b2 are equal (modulo renaming of variables)
        B = false otherwise
     *)

  let rec eqBlock (b1, b2) =
    let G1, L1 = I.constBlock b1 in
    let G2, L2 = I.constBlock b2 in
    eqCtx (G1, G2) && eqList (L1, L2)
  (* sumbsumedCtx (G, W) = ()

        Invariant:
        Let G be a context of blocks
        and W a world
        Then the function returns () if every block in G
        is listed in W
        otherwise Error is raised
     *)

  let rec subsumedCtx = function
    | I.Null, W -> ()
    | I.Decl (G, I.BDec (_, (b, _))), W ->
        if List.exists (fun b' -> eqBlock (b, b')) Bs then ()
        else raise (Error "Dynamic world subsumption failed");
        subsumedCtx (G, W)
    | I.Decl (G, _), W -> subsumedCtx (G, W)
  (******************************)

  (* Checking clauses and goals *)

  (******************************)

  (* checkGoal W (G, V, occ) = ()
        iff all (embedded) subgoals in V satisfy world spec W
        Effect: raises Error' (occ', msg) otherwise

        Invariant: G |- V : type, V nf
     *)

  let rec checkGoal = function
    | W, (G, I.Root (I.Const a, S), occ) ->
        let W' = W.getWorlds a in
        subsumedWorld a W' W;
        subsumedCtx (G, W)
    | W, (G, I.Pi ((D, _), V2), occ) ->
        checkGoal W (decUName (G, D), V2, P.body occ)
  (* checkClause (G, V, W, occ) = ()
       iff all subgoals in V satisfy world spec W
       Effect: raises Error' (occ', msg) otherwise

       Invariant: G |- V : type, V nf
       occ is occurrence of V in current clause
     *)

  let rec checkClause = function
    | W, (G, I.Root (a, S), occ) -> ()
    | W, (G, I.Pi ((D, I.Maybe), V2), occ) ->
        checkClause W (decEName (G, D), V2, P.body occ)
    | W, (G, I.Pi ((D, I.No), V2), occ) ->
        checkClause W (decEName (G, D), V2, P.body occ);
        checkGoal W (G, V1, P.label occ)

  let rec checkConDec W (I.ConDec (s, m, k, status, V, L)) =
    checkClause W (I.Null, V, P.top)
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
    | cid :: [] -> Block (cid, I.constBlock cid)
    | cid :: cids -> Plus (Block (cid, I.constBlock cid), worldsToReg' cids)
  (* init b (G, L) raises Success iff V is empty
       or none of the remaining declarations are relevant to b
       otherwise fails by returning ()
       Initial continuation for_sml world checker

       Invariant: G |- L dlist, L nf
    *)

  let rec init = function
    | _, Vs ->
        Trace.success ();
        raise (Success (Whnf.normalize Vs))
    | G, (V, s) ->
        Trace.unmatched (G, subGoalToDList (Whnf.normalize (V, s)));
        ()
  (* accR ((G, (V, s)), R, k)   raises Success
       iff V[s] = {L1}{L2} P  such that R accepts L1
           and k ((G, L1), L2) succeeds
       otherwise fails by returning ()
       Invariant: G |- (V s) type, L nf
                  R regular world expression
       trails at choice points to undo EVar instantiations during matching
    *)

  let rec accR = function
    | GVs, One, k -> k GVs
    | GVs, Block (c, (someDecs, piDecs)), k -> (
        (* G |- t : someDecs *)
        let t = createEVarSub (G, someDecs) in
        let _ =
          Trace.matchBlock
            ((G, subGoalToDList (Whnf.normalize (V, s))), Seq (1, piDecs, t))
        in
        let k' =
         fun (G', Vs') ->
          if noConstraints (G, t) then k (G', Vs')
          else (
            Trace.constraintsRemain ();
            ())
        in
        try
          accR
            ( (decUName (G, I.BDec (None, (c, t))), (V, I.comp (s, I.shift))),
              Seq (1, piDecs, I.comp (t, I.shift)),
              k' )
        with Success V ->
          raise
            (Success
               (Whnf.normalize
                  (I.Pi ((I.BDec (None, (c, t)), I.Maybe), V), I.id))))
    | (G, (V, s)), L', k ->
        if Unify.unifiable (G, (V1, s), (V1', t)) then
          accR
            ( (G, (V2, I.Dot (I.Exp (I.Root (I.Proj (I.Bidx 1, j), I.Nil)), s))),
              Seq
                ( j + 1,
                  L2',
                  I.Dot (I.Exp (I.Root (I.Proj (I.Bidx 1, j), I.Nil)), t) ),
              k )
        else (
          Trace.mismatch (G, (V1, I.id), (V1', t));
          ())
    | GVs, Seq (_, [], t), k -> k GVs
    | GVs, R, k ->
        Trace.missing (G, R);
        ()
    | GVs, Plus (r1, r2), k ->
        Cs.CSManager.trail (fun () -> accR (GVs, r1, k));
        accR (GVs, r2, k)
    | GVs, Star One, k -> k GVs
    | GVs, r, k ->
        Cs.CSManager.trail (fun () -> k GVs);
        accR (GVs, r', fun GVs' -> accR (GVs', r, k))
  (******************************)

  (* Worldifying clauses and goals *)

  (******************************)

  (* worldifyGoal (G, V, W, occ) = ()
       iff V = {{G'}} a @ S and G' satisfies worlds W
       Effect: raises Error' (occ', msg) otherwise

       Invariant: G |- V : type, V nf
    *)

  let rec worldifyGoal (G, V, W, occ) =
    try
      let b = I.targetFam V in
      let Wb = W.getWorlds b in
      let Rb = worldsToReg Wb in
      accR ((G, (V, I.id)), Rb, init);
      raise (Error' (occ, "World violation"))
    with Success V' -> V'
  (* worldifyClause (G, V, W, occ) = ()
       iff all subgoals in V satisfy world spec W
       Effect: raises Error' (occ', msg) otherwise

       Invariant: G |- V : type, V nf
       occ is occurrence of V in current clause
     *)

  let rec worldifyClause = function
    | G, V, W, occ -> V
    | G, I.Pi ((D, I.Maybe), V2), W, occ ->
        (*         val W1 = worldifyGoal (G, V1, W, P.label occ) *)
        let _ = print "{" in
        let W2 = worldifyClause (decEName (G, D), V2, W, P.body occ) in
        let _ = print "}" in
        I.Pi ((I.Dec (x, V1 (* W1*)), I.Maybe), W2)
    | G, I.Pi ((D, I.No), V2), W, occ ->
        let W1 = worldifyGoal (G, V1, W, P.label occ) in
        let W2 = worldifyClause (decEName (G, D), V2, W, P.body occ) in
        I.Pi ((I.Dec (x, W1), I.No), W2)
  (* worldcheck W a = ()
       iff all subgoals in all clauses defining a satisfy world spec W
       Effect: raises Error(msg) otherwise, where msg includes location
     *)

  let rec worldifyConDec W (c, I.ConDec (s, m, k, status, V, L)) =
    if !Global.chatter = 4 then
      print (Names.qidToString (Names.constQid c) ^ " ")
    else ();
    if !Global.chatter > 4 then Trace.clause c else ();
    try I.ConDec (s, m, k, status, worldifyClause (I.Null, V, W, P.top), L)
    with Error' (occ, msg) -> raise (Error (wrapMsg (c, occ, msg)))
  (* by invariant, other cases cannot apply *)

  let rec worldifyBlock = function
    | G, [] -> ()
    | G, D :: L ->
        let a = I.targetFam V in
        let W' = W.getWorlds a in
        checkClause W' (G, worldifyClause (I.Null, V, W', P.top), P.top);
        worldifyBlock (decUName (G, D), L)

  let rec worldifyBlocks = function
    | [] -> ()
    | b :: Bs -> (
        let _ = worldifyBlocks Bs in
        let Gsome, Lblock = I.constBlock b in
        let _ = print "|" in
        try worldifyBlock (Gsome, Lblock)
        with Error' (occ, s) ->
          raise (Error (wrapMsgBlock (b, occ, "World not hereditarily closed")))
        )

  let rec worldifyWorld (T.Worlds Bs) = worldifyBlocks Bs

  let rec worldify a =
    let W = W.getWorlds a in
    let _ = print "[?" in
    let W' = worldifyWorld W in
    let _ = print ";" in
    let _ =
      if !Global.chatter > 3 then
        print
          ("World checking family "
          ^ Names.qidToString (Names.constQid a)
          ^ ":\n")
      else ()
    in
    let condecs =
      map
        (fun (I.Const c) ->
          try worldifyConDec W (c, I.sgnLookup c)
          with Error' (occ, s) -> raise (Error (wrapMsg (c, occ, s))))
        (Index.lookup a)
    in
    let _ =
      map
        (fun condec ->
          print "#";
          checkConDec W condec)
        condecs
    in
    let _ = print "]" in
    let _ = if !Global.chatter = 4 then print "\n" else () in
    condecs

  let worldify = worldify

  let worldifyGoal =
   fun (G, V) -> worldifyGoal (G, V, W.getWorlds (I.targetFam V), P.top)
end

(* functor Worldify *)
