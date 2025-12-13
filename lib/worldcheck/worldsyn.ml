(* World Checking *)
(* Author: Carsten Schuermann *)
(* Modified: Frank Pfenning *)

functor (* GEN BEGIN FUNCTOR DECL *) WorldSyn
  (structure Global : GLOBAL
   structure Whnf : WHNF
   (*! sharing Whnf.IntSyn = IntSyn !*)
   structure Index : INDEX
   (*! sharing Index.IntSyn = IntSyn !*)
   structure Names : NAMES
   (*! sharing Names.IntSyn = IntSyn !*)
   structure Unify : UNIFY
   (*! sharing Unify.IntSyn = IntSyn !*)
   structure Abstract : ABSTRACT
   (*! sharing Abstract.IntSyn = IntSyn !*)
   structure Constraints : CONSTRAINTS
   (*! sharing Constraints.IntSyn = IntSyn !*)
   (*! structure CSManager : CS_MANAGER !*)
   (*! sharing CSManager.IntSyn = IntSyn !*)
   structure Subordinate : SUBORDINATE
   (*! sharing Subordinate.IntSyn = IntSyn !*)
   structure Print : PRINT
   (*! sharing Print.IntSyn = IntSyn !*)

   structure Table : TABLE where type key = int

   (*! structure Paths : PATHS !*)
   structure Origins : ORIGINS
   (*! sharing Origins.Paths = Paths !*)
     (*! sharing Origins.IntSyn = IntSyn !*)
   structure Timers : TIMERS)
   : WORLDSYN =
struct
  structure I = IntSyn
  structure T = Tomega
  structure P = Paths
  structure F = Print.Formatter

  exception Error of string

  exception Error' of P.occ * string

  (* copied from terminates/reduces.fun *)
  fun wrapMsg (c, occ, msg) =
      (case Origins.originLookup c
         of (fileName, NONE) => (fileName ^ ":" ^ msg)
          | (fileName, SOME occDec) =>
                (P.wrapLoc' (P.Loc (fileName, P.occToRegionDec occDec occ),
                             Origins.linesInfoLookup (fileName),
                             "While checking constant " ^ Names.qidToString (Names.constQid c) ^ ":\n" ^ msg)))

  type dlist = IntSyn.dec list


  local



    (* GEN BEGIN TAG OUTSIDE LET *) val worldsTable : T.worlds Table.table = Table.new (0) (* GEN END TAG OUTSIDE LET *)
    fun reset () = Table.clear worldsTable
    fun insert (cid, W) = Table.insert worldsTable (cid, W)
    fun getWorlds (b) =
        (case Table.lookup worldsTable b
           of NONE => raise Error ("Family " ^ Names.qidToString (Names.constQid b) ^ " has no worlds declaration")
            | SOME (Wb) => Wb)

    (* subsumedTable
       For each family a that is world-checked, this
       contains the subordinate families b whose worlds
       subsume that of a modulo subordination
    *)
    (* GEN BEGIN TAG OUTSIDE LET *) val subsumedTable : unit Table.table = Table.new (0) (* GEN END TAG OUTSIDE LET *)
    fun subsumedReset () = Table.clear subsumedTable
    fun subsumedInsert (cid) = Table.insert subsumedTable (cid, ())
    fun subsumedLookup (cid) =
        (case Table.lookup subsumedTable cid
           of NONE => false
            | SOME _ => true)

    (* Regular world expressions R
       Invariants:
       If R = (D1,...,Dn)[s] then G |- s : G' and G' |- D1,...,Dn ctx
       If R = r* then r = 1 or r does not accept the empty world
    *)
    datatype reg                        (* Regular world expressions  *)
      = Block of I.dctx * dlist         (* R ::= LD                   *)
      | Seq of dlist * I.sub            (*     | (D1,...,Dn)[s]       *)
      | Star of reg                     (*     | R*                   *)
      | Plus of reg * reg               (*     | R1 + R2              *)
      | One                             (*     | 1                    *)

    exception Success                   (* signals worldcheck success *)


    (* Format a regular world *)
    fun formatReg r =
        (case r
           of Block (G, dl) =>
              Print.formatDecList (G, dl)
            (* Is this correct? - gaw *)
            (* Fixed June 3, 2009 -fp,cs *)
            | Seq (dl, s) =>
              Print.formatDecList' (I.Null, (dl, s))
            | Star r =>
              F.Hbox ([F.String "(", formatReg r, F.String ")*"])
            | Plus (r1, r2) =>
              F.HVbox ([F.String "(", formatReg r1, F.String ")",
                        F.Break, F.String "|", F.Space,
                        F.String "(", formatReg r2, F.String ")"])
            | One =>
              F.String "1")

    (* Format a subsumption failure judgment
       msg: Prefix for the message
       dl : declaration list
       Rb : regular world
       b : family
       Displays:

         msg for family b:
         G |- dl </: Rb
     *)
    fun formatSubsump msg (G, dl, Rb, b) =
        (*
            F.HVbox ([F.String ((Names.qidToString (Names.constQid b)) ^ ":")])
        *)
        F.HVbox ([F.String msg, F.Space, F.String "for family", F.Space,
                  F.String ((Names.qidToString (Names.constQid b)) ^ ":"),
                  F.Break, (* F.Newline (), *)
                  (* Do not print some-variables; reenable if necessary *)
                  (* June 3, 2009 -fp,cs *)
                  (* Print.formatCtx(I.Null, G), F.Break, F.String "|-", F.Space, *)
                  Print.formatDecList (G, dl), F.Break, F.String ("</:"), F.Space,
                  formatReg Rb])

    (* createEVarSub G G' = s

       Invariant:
       If   G is a context
       and  G' is a context
       then G |- s : G'
    *)
    fun (* GEN BEGIN FUN FIRST *) createEVarSub (G, I.Null) = I.Shift (I.ctxLength G) (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) createEVarSub (G, I.Decl(G', D as I.Dec (_, V))) =
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val s = createEVarSub (G, G') (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val V' = I.EClo (V, s) (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val X = I.newEVar (G, V') (* GEN END TAG OUTSIDE LET *)
        in
          I.Dot (I.Exp X, s)
        end (* GEN END FUN BRANCH *)

    (* from cover.fun *)
    (* collectConstraints (Xs) = constrs
       collect all the constraints that may be attached to EVars in Xs

       try simplifying away the constraints in case they are "hard"
    *)
    fun (* GEN BEGIN FUN FIRST *) collectConstraints (nil) = nil (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) collectConstraints (I.EVar (_, _, _, ref nil)::Xs) =
          collectConstraints Xs (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) collectConstraints (I.EVar (_, _, _, ref constrs)::Xs) =
          (* constrs <> nil *)
          Constraints.simplify constrs @ collectConstraints Xs (* GEN END FUN BRANCH *)

    (* collectEVars (G, s, Xs) = Xs'
       adds all uninstantiated EVars from s to Xs to obtain Xs'
       Invariant: s is EVar substitutions
    *)
    fun (* GEN BEGIN FUN FIRST *) collectEVars (G, I.Dot (I.Exp X, s), Xs) =
           collectEVars (G, s, Abstract.collectEVars (G, (X, I.id), Xs)) (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) collectEVars (G, I.Shift _, Xs) = Xs (* GEN END FUN BRANCH *)
      (* other cases impossible by invariants since s is EVarSubst *)

    (* noConstraints (G, s) = true iff there are no remaining constraints in s
       Invariants: s is an EVar substitution X1...Xn.^k
    *)
    fun noConstraints (G, s) =
        (case collectConstraints (collectEVars (G, s, nil))
           of nil => true
            | _ => false)
    (* end from cover.fun *)

    (************)
    (* Printing *)
    (************)

    (* Declarations *)
    fun formatD (G, D) =
          F.Hbox (F.String "{" :: Print.formatDec (G, D) :: F.String "}" :: nil)

    (* Declaration lists *)
    fun (* GEN BEGIN FUN FIRST *) formatDList (G, nil, t) = nil (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) formatDList (G, D :: nil, t) =
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val D' = I.decSub (D, t) (* GEN END TAG OUTSIDE LET *)
        in
          formatD (G, D') :: nil (* Names.decUName (G, I.decSub(D, t)) *)
        end (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) formatDList (G, D :: L, t) =
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val D' = I.decSub (D, t) (* GEN END TAG OUTSIDE LET *) (* Names.decUName (G, I.decSub (D, t)) *)
        in
          formatD (G, D') :: F.Break
          :: formatDList (I.Decl (G, D'), L, I.dot1 t)
        end (* GEN END FUN BRANCH *)

    (*
    fun hypsToDList (I.Root _) = nil
      | hypsToDList (I.Pi ((D, _), V)) =
          D::hypsToDList V
    *)

    (* Hypotheses and declaration lists *)
    fun wGoalToString ((G, L), Seq (piDecs, t)) =
        F.makestring_fmt (F.HVbox [F.HVbox (formatDList (G, L, I.id)), F.Break,
                                   F.String "<|", F.Break,
                                   F.HVbox (formatDList (G, piDecs, t))])

    (* Declaration list *)
    fun worldToString (G, Seq (piDecs, t)) =
          F.makestring_fmt (F.HVbox (formatDList (G, piDecs, t)))

    (* Hypotheses *)
    fun hypsToString (G, L) =
          F.makestring_fmt (F.HVbox (formatDList (G, L, I.id)))

    (* Mismatch between hypothesis and world declaration *)
    fun mismatchToString (G, (V1, s1), (V2, s2)) =
        F.makestring_fmt (F.HVbox [Print.formatExp (G, I.EClo (V1, s1)), F.Break,
                                   F.String "<>", F.Break,
                                   Print.formatExp (G, I.EClo (V2, s2))])

    (***********)
    (* Tracing *)
    (***********)

    structure Trace :
    sig
      val clause : I.cid -> unit
      val constraintsRemain : unit -> unit
      val matchBlock : (I.dctx * dlist) * reg -> unit
      val unmatched : I.dctx * dlist -> unit
      val missing : I.dctx * reg -> unit
      val mismatch : I.dctx * I.eclo * I.eclo -> unit
      val success : unit -> unit
    end =
    struct
      fun clause (c) =
          print ("World checking clause " ^ Names.qidToString (Names.constQid c) ^ "\n")
      fun constraintsRemain () =
          if !Global.chatter > 7
            then print ("Constraints remain after matching hypotheses against context block\n")
          else ()
      fun matchBlock (GL, R) =          (* R = (D1,...,Dn)[t] *)
          if !Global.chatter > 7
            then print ("Matching:\n" ^ wGoalToString (GL, R) ^ "\n")
          else ()
      fun unmatched GL =
          if !Global.chatter > 7
            then print ("Unmatched hypotheses:\n" ^ hypsToString GL ^ "\n")
          else ()
      fun missing (G, R) =              (* R = (D1,...,Dn)[t] *)
          if !Global.chatter > 7
            then print ("Missing hypotheses:\n" ^ worldToString (G, R) ^ "\n")
          else ()
      fun mismatch (G, Vs1, Vs2) =
          if !Global.chatter > 7
            then print ("Mismatch:\n" ^ mismatchToString (G, Vs1, Vs2) ^ "\n")
          else ()
      fun success () =
          if !Global.chatter > 7
            then print ("Success\n")
          else ()
    end

    fun decUName (G, D) = I.Decl (G, Names.decUName (G, D))
    fun decEName (G, D) = I.Decl (G, Names.decEName (G, D))

    (**************************************)
    (* Matching hypotheses against worlds *)
    (**************************************)

    fun (* GEN BEGIN FUN FIRST *) subGoalToDList (I.Pi ((D, _), V)) = D::subGoalToDList(V) (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) subGoalToDList (I.Root _) = nil (* GEN END FUN BRANCH *)

    (* worldsToReg (Worlds [c1,...,cn]) = R
       W = R, except that R is a regular expression
       with non-empty contextblocks as leaves
    *)
    fun (* GEN BEGIN FUN FIRST *) worldsToReg (T.Worlds nil) = One (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) worldsToReg (T.Worlds cids) = Star (worldsToReg' cids) (* GEN END FUN BRANCH *)
    and (* GEN BEGIN FUN FIRST *) worldsToReg' (cid::nil) = Block (I.constBlock cid) (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) worldsToReg' (cid::cids) =
          Plus (Block (I.constBlock cid), worldsToReg' cids) (* GEN END FUN BRANCH *)

    (* init b (G, L) raises Success iff V is empty
       or none of the remaining declarations are relevant to b
       otherwise fails by returning ()
       Initial continuation for world checker

       Invariant: G |- L dlist, L nf
    *)
    fun (* GEN BEGIN FUN FIRST *) init b (_, nil) = ( Trace.success () ; raise Success) (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) init b (G, L as (D1 as I.Dec (_, V1))::L2) =
        if Subordinate.belowEq (I.targetFam V1, b)
          then ( Trace.unmatched (G, L) ; () )
        else init b (decUName (G, D1), L2) (* GEN END FUN BRANCH *)

    (* accR ((G, L), R, k)   raises Success
       iff L = L1,L2 such that R accepts L1
           and k ((G, L1), L2) succeeds
       otherwise fails by returning ()
       Invariant: G |- L dlist, L nf
                  R regular world expression
       trails at choice points to undo EVar instantiations during matching
    *)
    fun (* GEN BEGIN FUN FIRST *) accR (GL, One, b, k) = k GL (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) accR (GL as (G, L), Block (someDecs, piDecs), b, k) =
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val t = createEVarSub (G, someDecs) (* GEN END TAG OUTSIDE LET *) (* G |- t : someDecs *)
          (* GEN BEGIN TAG OUTSIDE LET *) val _ = Trace.matchBlock (GL, Seq (piDecs, t)) (* GEN END TAG OUTSIDE LET *)
          (* if block matches, check for remaining constraints *)
          (* GEN BEGIN TAG OUTSIDE LET *) val k' = ((* GEN BEGIN FUNCTION EXPRESSION *) fn GL' => if noConstraints (G, t)
                                then k GL'
                              else ( Trace.constraintsRemain () ; () ) (* GEN END FUNCTION EXPRESSION *)) (* GEN END TAG OUTSIDE LET *)
        in
          accR (GL, Seq (piDecs, t), b, k')
        end (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) accR ((G, L as (D as I.Dec (_, V1))::L2),
              L' as Seq (B' as I.Dec (_, V1')::L2', t), b, k) =
        if Unify.unifiable (G, (V1, I.id), (V1', t))
          then accR ((decUName (G, D), L2), Seq (L2', I.dot1 t), b, k)
        else if Subordinate.belowEq (I.targetFam V1, b)
               then (* relevant to family b, fail *)
                 ( Trace.mismatch (G, (V1, I.id), (V1', t)) ; () )
             else (* not relevant to family b, skip in L *)
               accR ((decUName (G, D), L2), Seq (B', I.comp(t, I.shift)), b, k) (* GEN END FUN BRANCH *)
               (* fixed bug in previous line; was: t instead of t o ^ *)
               (* Mon May 7 2007 -fp *)
      | (* GEN BEGIN FUN BRANCH *) accR (GL, Seq (nil, t), b, k) = k GL (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) accR (GL as (G, nil), R as Seq (L', t), b, k) =
          ( Trace.missing (G, R); () ) (* GEN END FUN BRANCH *)  (* L is missing *)
      | (* GEN BEGIN FUN BRANCH *) accR (GL, Plus (r1, r2), b, k) =
          ( CSManager.trail ((* GEN BEGIN FUNCTION EXPRESSION *) fn () => accR (GL, r1, b, k) (* GEN END FUNCTION EXPRESSION *)) ;
            accR (GL, r2, b, k) ) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) accR (GL, Star (One), b, k) = k GL (* GEN END FUN BRANCH *) (* only possibility for non-termination in next rule *)
      | (* GEN BEGIN FUN BRANCH *) accR (GL, r as Star(r'), b, k) = (* r' does not accept empty declaration list *)
          ( CSManager.trail ((* GEN BEGIN FUNCTION EXPRESSION *) fn () => k GL (* GEN END FUNCTION EXPRESSION *)) ;
            accR (GL, r', b, (* GEN BEGIN FUNCTION EXPRESSION *) fn GL' => accR (GL', r, b, k) (* GEN END FUNCTION EXPRESSION *))) (* GEN END FUN BRANCH *)

    (* checkSubsumedBlock (G, someDecs, piDecs, Rb, b) = ()
       iff block SOME someDecs. PI piDecs is subsumed by Rb
       Effect: raises Error (msg) otherwise

       Invariants: Rb = reg (worlds (b))
    *)
    fun checkSubsumedBlock (G, L', Rb, b) =
        (( accR ((G, L'), Rb, b, init b) ;
          raise Error (F.makestring_fmt (formatSubsump "World subsumption failure" (G, L', Rb, b))))
         handle Success => ())

    (* checkSubsumedWorlds (Wa, Rb, b) = ()
       iff Wa is subsumed by Rb
       Effect: raises Error (msg) otherwise

       Invariants: Rb = reg (worlds (b))
    *)
    fun (* GEN BEGIN FUN FIRST *) checkSubsumedWorlds (nil, Rb, b) = () (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) checkSubsumedWorlds (cid::cids, Rb, b) =
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val (someDecs, piDecs) = I.constBlock cid (* GEN END TAG OUTSIDE LET *)
        in
          checkSubsumedBlock (Names.ctxName(someDecs), piDecs, Rb, b);
          checkSubsumedWorlds (cids, Rb, b)
        end (* GEN END FUN BRANCH *)

    (* checkBlocks W (G, V, occ) = ()
       iff V = {{G'}} a @ S and G' satisfies worlds W
       Effect: raises Error'(occ, msg) otherwise

       Invariants: G |- V : type, V nf
    *)
    fun checkBlocks (T.Worlds cids) (G, V, occ) =
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val b = I.targetFam V (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val Wb = getWorlds b handle Error (msg) => raise Error' (occ, msg) (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val Rb = worldsToReg Wb (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val _ = if subsumedLookup b
                    then ()
                  else ( checkSubsumedWorlds (cids, Rb, b) ;
                         subsumedInsert (b) )
                       handle Error (msg) => raise Error' (occ, msg) (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val L = subGoalToDList V (* GEN END TAG OUTSIDE LET *)
        in
          (accR ((G, L), Rb, b, init b);
           raise Error' (occ, F.makestring_fmt (formatSubsump "World violation" (G, L, Rb, b))))
        end
        handle Success => ()

    (******************************)
    (* Checking clauses and goals *)
    (******************************)

    (* checkClause (G, V, W, occ) = ()
       iff all subgoals in V satisfy world spec W
       Effect: raises Error' (occ', msg) otherwise

       Invariant: G |- V : type, V nf
       occ is occurrence of V in current clause
     *)
     fun (* GEN BEGIN FUN FIRST *) checkClause (G, I.Root (a, S), W, occ) = () (* GEN END FUN FIRST *)
       | (* GEN BEGIN FUN BRANCH *) checkClause (G, I.Pi ((D as I.Dec (_, V1), I.Maybe), V2), W, occ) =
         (checkClause (decEName (G, D), V2, W, P.body occ);
          checkGoal (G, V1, W, P.label occ)) (* GEN END FUN BRANCH *)
       | (* GEN BEGIN FUN BRANCH *) checkClause (G, I.Pi ((D as I.Dec (_, V1), I.No), V2), W, occ) =
         (checkBlocks W (G, V1, P.label occ);
          checkClause (decEName (G, D), V2, W, P.body occ);
          checkGoal (G, V1, W, P.label occ)) (* GEN END FUN BRANCH *)

     (* checkGoal (G, V, W, occ) = ()
        iff all (embedded) subgoals in V satisfy world spec W
        Effect: raises Error' (occ', msg) otherwise

        Invariant: G |- V : type, V nf
     *)
     (* Question: should dependent Pi's really be checked recursively? *)
     (* Thu Mar 29 09:38:20 2001 -fp *)
     and (* GEN BEGIN FUN FIRST *) checkGoal (G, I.Root (a, S), W, occ) = () (* GEN END FUN FIRST *)
       | (* GEN BEGIN FUN BRANCH *) checkGoal (G, I.Pi ((D as I.Dec (_, V1), _), V2), W, occ) =
         (checkGoal (decUName (G, D), V2, W, P.body occ);
          checkClause (G, V1, W, P.label occ)) (* GEN END FUN BRANCH *)

    (* worldcheck W a = ()
       iff all subgoals in all clauses defining a satisfy world spec W
       Effect: raises Error(msg) otherwise, where msg includes location
    *)
    fun worldcheck W a =
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val _ = if !Global.chatter > 3
                    then print ("World checking family " ^ Names.qidToString (Names.constQid a) ^ ":\n")
                  else () (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val _ = subsumedReset () (* GEN END TAG OUTSIDE LET *)      (* initialize table of subsumed families *)
          fun (* GEN BEGIN FUN FIRST *) checkAll nil = () (* GEN END FUN FIRST *)
            | (* GEN BEGIN FUN BRANCH *) checkAll (I.Const(c) :: clist) =
              (if !Global.chatter = 4
                 then print (Names.qidToString (Names.constQid c) ^ " ")
               else ();
               if !Global.chatter > 4 then Trace.clause c else ();
               checkClause (I.Null, I.constType c, W, P.top)
                 handle Error' (occ, msg) => raise Error (wrapMsg (c, occ, msg));
               checkAll clist) (* GEN END FUN BRANCH *)
            | (* GEN BEGIN FUN BRANCH *) checkAll (I.Def(d) :: clist) =
              (if !Global.chatter = 4
                 then print (Names.qidToString (Names.constQid d) ^ " ")
               else ();
               if !Global.chatter > 4 then Trace.clause d else ();
               checkClause (I.Null, I.constType d, W, P.top)
                 handle Error' (occ, msg) => raise Error (wrapMsg (d, occ, msg));
               checkAll clist) (* GEN END FUN BRANCH *)
          (* GEN BEGIN TAG OUTSIDE LET *) val _ = checkAll (Index.lookup a) (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val _ = if !Global.chatter = 4 then print "\n" else () (* GEN END TAG OUTSIDE LET *)
      in
        ()
      end

    (**************************)
    (* Checking Subordination *)
    (**************************)

    (*
       At present, worlds declarations must respect the
       current subordination relation in order to guarantee
       soundness.
    *)
    fun (* GEN BEGIN FUN FIRST *) ctxAppend (G, I.Null) = G (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) ctxAppend (G, I.Decl(G',D)) =
          I.Decl (ctxAppend (G, G'), D) (* GEN END FUN BRANCH *)

    (* checkSubordBlock (G, G', L') = ()
       Effect: raises Error(msg) if subordination is not respected
               in context block SOME G'. PI L'
       Invariants: G |- SOME G'. PI L' block
    *)
    fun checkSubordBlock (G, G', L) =
          checkSubordBlock' (ctxAppend (G, G'), L)
    and (* GEN BEGIN FUN FIRST *) checkSubordBlock' (G, (D as I.Dec(_,V))::L') =
          ( Subordinate.respectsN (G, V); (* is V nf?  Assume here: yes! *)
            checkSubordBlock' (I.Decl (G, D), L') ) (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) checkSubordBlock' (G, nil) = () (* GEN END FUN BRANCH *)

    (* conDecBlock (condec) = (Gsome, Lpi)
       if condec is a block declaration
       raise Error (msg) otherwise
    *)
    fun (* GEN BEGIN FUN FIRST *) conDecBlock (I.BlockDec (_, _, Gsome, Lpi)) = (Gsome, Lpi) (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) conDecBlock condec =
        raise Error ("Identifier " ^ I.conDecName condec
                     ^ " is not a block label") (* GEN END FUN BRANCH *)

    (* constBlock cid = (someDecs, piDecs)
       if cid is defined as a context block
       Effect: raise Error (msg) otherwise
    *)
    fun constBlock (cid) = conDecBlock (I.sgnLookup cid)

    (* checkSubordWorlds (W) = ()
       Effect: raises Error(msg) if subordination is not respected
               in some context block in W
    *)
    fun (* GEN BEGIN FUN FIRST *) checkSubordWorlds (nil) = () (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) checkSubordWorlds (cid::cids) =
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val (someDecs, piDecs) = constBlock cid (* GEN END TAG OUTSIDE LET *)
        in
          checkSubordBlock (I.Null, someDecs, piDecs) ;
          checkSubordWorlds cids
        end (* GEN END FUN BRANCH *)

    (* install (a, W) = ()
       install worlds declaration W for family a

       Effect: raises Error if W does not respect subordination
    *)
    fun install (a, W as T.Worlds(cids)) =
        ( checkSubordWorlds cids
            handle Subordinate.Error (msg) => raise Error (msg) ;
          insert (a, W) )

    fun uninstall a =
        case Table.lookup worldsTable a
          of NONE => false
           | SOME _ => (Table.delete worldsTable a; true)

    (* lookup (a) = SOME W if worlds declared for a, NONE otherwise *)
    fun lookup a = getWorlds a

    (* ctxToList G = L

       Invariant:
       G = L  (G is left associative, L is right associative)
    *)
    fun ctxToList (Gin) =
        let
          fun (* GEN BEGIN FUN FIRST *) ctxToList' (I.Null, G ) = G (* GEN END FUN FIRST *)
            | (* GEN BEGIN FUN BRANCH *) ctxToList' (I.Decl (G, D), G') =
            ctxToList' (G, D :: G') (* GEN END FUN BRANCH *)
        in
          ctxToList' (Gin, nil)
        end



    (* isSubsumed (W, b) = ()
       holds if the worlds associated with b are subsumed by W
       Effect: raises Error'(occ, msg) otherwise

       Invariants: G |- V : type, V nf
    *)
    fun isSubsumed (T.Worlds cids) b =
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val Wb = getWorlds b (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val Rb = worldsToReg Wb (* GEN END TAG OUTSIDE LET *)
        in
          if subsumedLookup b
            then ()
          else ( checkSubsumedWorlds (cids, Rb, b) ;
                subsumedInsert (b) )
        end

  in
    (* GEN BEGIN TAG OUTSIDE LET *) val reset = reset (* GEN END TAG OUTSIDE LET *)
    (* GEN BEGIN TAG OUTSIDE LET *) val install = install (* GEN END TAG OUTSIDE LET *)
    (* GEN BEGIN TAG OUTSIDE LET *) val lookup = lookup (* GEN END TAG OUTSIDE LET *)
    (* GEN BEGIN TAG OUTSIDE LET *) val uninstall = uninstall (* GEN END TAG OUTSIDE LET *)
    (* GEN BEGIN TAG OUTSIDE LET *) val worldcheck = worldcheck (* GEN END TAG OUTSIDE LET *)
    (* GEN BEGIN TAG OUTSIDE LET *) val ctxToList = ctxToList (* GEN END TAG OUTSIDE LET *)
    (* GEN BEGIN TAG OUTSIDE LET *) val isSubsumed = isSubsumed (* GEN END TAG OUTSIDE LET *)
    (* GEN BEGIN TAG OUTSIDE LET *) val getWorlds = getWorlds (* GEN END TAG OUTSIDE LET *)
  end

end (* GEN END FUNCTOR DECL *);  (* functor WorldSyn *)
