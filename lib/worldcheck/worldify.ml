(* Worldification and World-checking *)
(* Author: Carsten Schuermann *)
(* Modified: Frank Pfenning *)

functor (* GEN BEGIN FUNCTOR DECL *) Worldify
  (structure Global : GLOBAL
   (*! structure IntSyn : INTSYN !*)
   (*! structure Tomega : TOMEGA !*)
   (*! sharing Tomega.IntSyn = IntSyn !*)
   structure WorldSyn : WORLDSYN
   (*! sharing WorldSyn.IntSyn = IntSyn !*)
   (*! sharing WorldSyn.Tomega = Tomega !*)
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
   structure CSManager : CS_MANAGER
   (*! sharing CSManager.IntSyn = IntSyn !*)
   structure Subordinate : SUBORDINATE
   (*! sharing Subordinate.IntSyn = IntSyn !*)
   structure Print : PRINT
   (*! sharing Print.IntSyn = IntSyn !*)

   structure Table : TABLE where type key = int
   structure MemoTable : TABLE where type key = int * int
   structure IntSet : INTSET

   (*! structure Paths : PATHS !*)
   structure Origins : ORIGINS
   (*! sharing Origins.Paths = Paths !*)
   (*! sharing Origins.IntSyn = IntSyn !*)
       )
   : WORLDIFY =
struct
  (*! structure IntSyn = IntSyn !*)
  (*! structure Tomega = Tomega !*)
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
                             "Constant " ^ Names.qidToString (Names.constQid c) ^ ":" ^ msg)))

  fun wrapMsgBlock (c, occ, msg) =
      (case Origins.originLookup c
         of (fileName, NONE) => (fileName ^ ":" ^ msg)
          | (fileName, SOME occDec) =>
                (P.wrapLoc' (P.Loc (fileName, P.occToRegionDec occDec occ),
                             Origins.linesInfoLookup (fileName),
                             "Block " ^ Names.qidToString (Names.constQid c) ^ ":" ^ msg)))


  type dlist = IntSyn.dec list


  local
    structure W = WorldSyn

    (* Regular world expressions R
       Invariants:
       If R = (D1,...,Dn)[s] then G |- s : G' and G' |- D1,...,Dn ctx
       If R = r* then r = 1 or r does not accept the empty world
    *)
    datatype reg                        (* Regular world expressions  *)
      = Block of I.cid * (I.dctx * dlist)               (* R ::= LD                   *)
      | Seq of int * dlist * I.sub      (*     | (Di,...,Dn)[s]       *)
      | Star of reg                     (*     | R*                   *)
      | Plus of reg * reg               (*     | R1 + R2              *)
      | One                             (*     | 1                    *)

    exception Success of I.exp                  (* signals worldcheck success *)

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
    fun wGoalToString ((G, L), Seq (_, piDecs, t)) =
        F.makestring_fmt (F.HVbox [F.HVbox (formatDList (G, L, I.id)), F.Break,
                                   F.String "<|", F.Break,
                                   F.HVbox (formatDList (G, piDecs, t))])

    (* Declaration list *)
    fun worldToString (G, Seq (_, piDecs, t)) =
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
     fun (* GEN BEGIN FUN FIRST *) equivList (G, (_, nil), nil) = true (* GEN END FUN FIRST *)
       | (* GEN BEGIN FUN BRANCH *) equivList (G, (t, I.Dec (_, V1) :: L1), I.Dec (_, V2) :: L2) =
           (( Unify.unify (G, (V1, t), (V2, I.id))
            ; equivList (G, (I.dot1 t, L1), L2)
            ) handle Unify.Unify _ => false) (* GEN END FUN BRANCH *)
       | (* GEN BEGIN FUN BRANCH *) equivList _ = false (* GEN END FUN BRANCH *)


     (* equivBlock ((G, L), L') = B

        Invariant:
        If   G |- L block
        then B = true if there exists a substitution . |- t : G, s.t. L[t] = L'
             B = false otherwise
     *)
     fun equivBlock ((G, L), L') =
         let
           (* GEN BEGIN TAG OUTSIDE LET *) val t = createEVarSub (I.Null, G) (* GEN END TAG OUTSIDE LET *)
         in
           equivList (I.Null, (t, L), L')
         end

     (* equivBlocks W L = B

        Invariant:
        Let W be a world and L be a block.
        B = true if exists L' in W such that L = L'
        B = false otherwise
     *)
     fun (* GEN BEGIN FUN FIRST *) equivBlocks W1 nil = true (* GEN END FUN FIRST *)
       | (* GEN BEGIN FUN BRANCH *) equivBlocks nil L' = false (* GEN END FUN BRANCH *)
       | (* GEN BEGIN FUN BRANCH *) equivBlocks (b :: W1) L' =
           equivBlock (I.constBlock b, L')
           orelse equivBlocks W1 L' (* GEN END FUN BRANCH *)

     (* strengthen a (t, L) = L'

        Invariant:
        If   a is a type family,
        and  . |- t : G
        and  G |- L block
        then . |- L' block
        where V \in L and not V < a then V \in L'
        and   V \in L and V < a then not V \in L'
     *)
     fun (* GEN BEGIN FUN FIRST *) strengthen a (t, nil) = nil (* GEN END FUN FIRST *)
       | (* GEN BEGIN FUN BRANCH *) strengthen a (t, (D as I.Dec (_, V)) :: L) =
         if Subordinate.below (I.targetFam V, a) then (I.decSub (D, t) :: strengthen a (I.dot1 t, L))
         else strengthen a (I.Dot (I.Undef,  t), L) (* GEN END FUN BRANCH *)


     (* subsumedBlock a W1 (G, L) = ()

        Invariant:
        If   a is a type family
        and  W1 the world in which the callee is defined
        and (G, L) one block in the world of the caller
        Then the function returns () if (G, L) is subsumed by W1
        otherwise Error is raised
     *)
     fun subsumedBlock a W1 (G, L) =
         let
           (* GEN BEGIN TAG OUTSIDE LET *) val t = createEVarSub (I.Null, G) (* GEN END TAG OUTSIDE LET *) (* G |- t : someDecs *)
           (* GEN BEGIN TAG OUTSIDE LET *) val L' = strengthen a (t, L) (* GEN END TAG OUTSIDE LET *)
         in
           if equivBlocks W1 L' then () else raise Error "Static world subsumption failed"
         end

     (* subsumedBlocks a W1 W2 = ()

        Invariant:
        Let W1 be the world in which the callee is defined
        Let W2 be the world in which the caller is defined
        Then the function returns () if W2 is subsumed by W1
        otherwise Error is raised
     *)
     fun (* GEN BEGIN FUN FIRST *) subsumedBlocks a W1 nil = () (* GEN END FUN FIRST *)
       | (* GEN BEGIN FUN BRANCH *) subsumedBlocks a W1 (b :: W2) =
           ( subsumedBlock a W1 (I.constBlock b)
           ; subsumedBlocks a W1 W2
           ) (* GEN END FUN BRANCH *)

     (* subsumedWorld a W1 W2 = ()

        Invariant:
        Let W1 be the world in which the callee is defined
        Let W2 be the world in which the caller is defined
        Then the function returns () if W2 is subsumed by W1
        otherwise Error is raised
     *)
     fun subsumedWorld a (T.Worlds W1) (T.Worlds W2) =
         subsumedBlocks a W1 W2


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
     fun (* GEN BEGIN FUN FIRST *) eqCtx (I.Null, I.Null)  = true (* GEN END FUN FIRST *)
       | (* GEN BEGIN FUN BRANCH *) eqCtx (I.Decl (G1, D1), I.Decl (G2, D2)) =
           eqCtx (G1, G2) andalso Conv.convDec ((D1, I.id), (D2, I.id)) (* GEN END FUN BRANCH *)
       | (* GEN BEGIN FUN BRANCH *) eqCtx _ = false (* GEN END FUN BRANCH *)

     (* eqList (L1, L2) = B

        Invariant:
        Let  L1, L2 lists of declarations (as the occur in a block).
        B = true if L1 and L2 are equal (modulo renaming of variables)
        B = false otherwise
     *)
     fun (* GEN BEGIN FUN FIRST *) eqList (nil, nil) = true (* GEN END FUN FIRST *)
       | (* GEN BEGIN FUN BRANCH *) eqList (D1 :: L1, D2 :: L2) =
           Conv.convDec ((D1, I.id), (D2, I.id)) andalso eqList (L1, L2) (* GEN END FUN BRANCH *)
       | (* GEN BEGIN FUN BRANCH *) eqList _ = false (* GEN END FUN BRANCH *)


     (* eqBlock (b1, b2) = B

        Invariant:
        Let  b1, b2 blocks.
        B = true if b1 and b2 are equal (modulo renaming of variables)
        B = false otherwise
     *)
     fun eqBlock (b1, b2) =
         let
           (* GEN BEGIN TAG OUTSIDE LET *) val (G1, L1) = I.constBlock b1 (* GEN END TAG OUTSIDE LET *)
           (* GEN BEGIN TAG OUTSIDE LET *) val (G2, L2) = I.constBlock b2 (* GEN END TAG OUTSIDE LET *)
         in
           eqCtx (G1, G2) andalso eqList (L1, L2)
         end


     (* sumbsumedCtx (G, W) = ()

        Invariant:
        Let G be a context of blocks
        and W a world
        Then the function returns () if every block in G
        is listed in W
        otherwise Error is raised
     *)
     fun (* GEN BEGIN FUN FIRST *) subsumedCtx (I.Null, W) = () (* GEN END FUN FIRST *)
       | (* GEN BEGIN FUN BRANCH *) subsumedCtx (I.Decl (G, I.BDec (_, (b, _))), W as T.Worlds Bs) =
          ( if List.exists ((* GEN BEGIN FUNCTION EXPRESSION *) fn b' => eqBlock (b, b') (* GEN END FUNCTION EXPRESSION *)) Bs
              then () else raise Error "Dynamic world subsumption failed"
          ; subsumedCtx (G, W)
          ) (* GEN END FUN BRANCH *)
       | (* GEN BEGIN FUN BRANCH *) subsumedCtx (I.Decl (G, _), W as T.Worlds Bs) =
          subsumedCtx (G, W) (* GEN END FUN BRANCH *)



    (******************************)
    (* Checking clauses and goals *)
    (******************************)

     (* checkGoal W (G, V, occ) = ()
        iff all (embedded) subgoals in V satisfy world spec W
        Effect: raises Error' (occ', msg) otherwise

        Invariant: G |- V : type, V nf
     *)
     fun (* GEN BEGIN FUN FIRST *) checkGoal W (G, I.Root (I.Const a, S), occ) =
         let
           (* GEN BEGIN TAG OUTSIDE LET *) val W' = W.getWorlds a (* GEN END TAG OUTSIDE LET *)
         in
           ( subsumedWorld a W' W
           ; subsumedCtx (G, W)
           )
         end (* GEN END FUN FIRST *)
       | (* GEN BEGIN FUN BRANCH *) checkGoal W (G, I.Pi ((D, _), V2), occ) =
           checkGoal W (decUName (G, D), V2, P.body occ) (* GEN END FUN BRANCH *)

    (* checkClause (G, V, W, occ) = ()
       iff all subgoals in V satisfy world spec W
       Effect: raises Error' (occ', msg) otherwise

       Invariant: G |- V : type, V nf
       occ is occurrence of V in current clause
     *)
     fun (* GEN BEGIN FUN FIRST *) checkClause W (G, I.Root (a, S), occ) = () (* GEN END FUN FIRST *)
       | (* GEN BEGIN FUN BRANCH *) checkClause W (G, I.Pi ((D as I.Dec (_, V1), I.Maybe), V2), occ) =
         checkClause W (decEName (G, D), V2, P.body occ) (* GEN END FUN BRANCH *)
       | (* GEN BEGIN FUN BRANCH *) checkClause W (G, I.Pi ((D as I.Dec (_, V1), I.No), V2), occ) =
         (checkClause W (decEName (G, D), V2, P.body occ);
          checkGoal W (G, V1, P.label occ)) (* GEN END FUN BRANCH *)

     fun checkConDec W (I.ConDec (s, m, k, status, V, L)) =
           checkClause W (I.Null, V, P.top)



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
    and (* GEN BEGIN FUN FIRST *) worldsToReg' (cid::nil) = Block (cid, I.constBlock cid) (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) worldsToReg' (cid::cids) =
          Plus (Block (cid, I.constBlock cid), worldsToReg' cids) (* GEN END FUN BRANCH *)

    (* init b (G, L) raises Success iff V is empty
       or none of the remaining declarations are relevant to b
       otherwise fails by returning ()
       Initial continuation for world checker

       Invariant: G |- L dlist, L nf
    *)
    fun (* GEN BEGIN FUN FIRST *) init (_, Vs as (I.Root _, s)) =
        (Trace.success () ;
         raise Success (Whnf.normalize Vs)) (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) init (G, (V as I.Pi ((D1 as I.Dec (_, V1), _), V2), s)) =
        (Trace.unmatched (G, subGoalToDList (Whnf.normalize (V, s))) ; ()) (* GEN END FUN BRANCH *)

    (* accR ((G, (V, s)), R, k)   raises Success
       iff V[s] = {L1}{L2} P  such that R accepts L1
           and k ((G, L1), L2) succeeds
       otherwise fails by returning ()
       Invariant: G |- (V s) type, L nf
                  R regular world expression
       trails at choice points to undo EVar instantiations during matching
    *)
    fun (* GEN BEGIN FUN FIRST *) accR (GVs, One, k) = k GVs (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) accR (GVs as (G, (V, s)), Block (c, (someDecs, piDecs)), k) =
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val t = createEVarSub (G, someDecs) (* GEN END TAG OUTSIDE LET *) (* G |- t : someDecs *)
          (* GEN BEGIN TAG OUTSIDE LET *) val _ = Trace.matchBlock ((G, subGoalToDList (Whnf.normalize (V, s))), Seq (1, piDecs, t)) (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val k' = ((* GEN BEGIN FUNCTION EXPRESSION *) fn (G', Vs') =>
                    if noConstraints (G, t)
                      then k (G', Vs')
                    else (Trace.constraintsRemain (); ()) (* GEN END FUNCTION EXPRESSION *)) (* GEN END TAG OUTSIDE LET *)
      
        in
          accR ((decUName (G, I.BDec (NONE, (c, t))), (V, I.comp (s, I.shift))),
                Seq (1, piDecs, I.comp (t, I.shift)), k')
          handle Success V => raise Success (Whnf.normalize (I.Pi ((I.BDec (NONE, (c, t)), I.Maybe), V), I.id))
        end (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) accR ((G, (V as I.Pi ((D as I.Dec (_, V1), _), V2), s)),
              L' as Seq (j, I.Dec (_, V1')::L2', t), k) =
        if Unify.unifiable (G, (V1, s), (V1', t))
          then accR ((G, (V2, I.Dot (I.Exp (I.Root (I.Proj (I.Bidx 1, j), I.Nil)), s))),
                     Seq (j+1, L2', I.Dot (I.Exp (I.Root (I.Proj (I.Bidx 1, j), I.Nil)), t)), k)
        else  (Trace.mismatch (G, (V1, I.id), (V1', t)) ; ()) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) accR (GVs, Seq (_, nil, t), k) = k GVs (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) accR (GVs as (G, (I.Root _, s)), R as Seq (_, L', t), k) =
          ( Trace.missing (G, R); () ) (* GEN END FUN BRANCH *)  (* L is missing *)
      | (* GEN BEGIN FUN BRANCH *) accR (GVs, Plus (r1, r2), k) =
          ( CSManager.trail ((* GEN BEGIN FUNCTION EXPRESSION *) fn () => accR (GVs, r1, k) (* GEN END FUNCTION EXPRESSION *)) ;
            accR (GVs, r2, k) ) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) accR (GVs, Star (One), k) = k GVs (* GEN END FUN BRANCH *) (* only possibility for non-termination in next rule *)
      | (* GEN BEGIN FUN BRANCH *) accR (GVs, r as Star(r'), k) = (* r' does not accept empty declaration list *)
          ( CSManager.trail ((* GEN BEGIN FUNCTION EXPRESSION *) fn () => k GVs (* GEN END FUNCTION EXPRESSION *)) ;
            accR (GVs, r', (* GEN BEGIN FUNCTION EXPRESSION *) fn GVs' => accR (GVs', r, k) (* GEN END FUNCTION EXPRESSION *))) (* GEN END FUN BRANCH *)


    (******************************)
    (* Worldifying clauses and goals *)
    (******************************)

    (* worldifyGoal (G, V, W, occ) = ()
       iff V = {{G'}} a @ S and G' satisfies worlds W
       Effect: raises Error' (occ', msg) otherwise

       Invariant: G |- V : type, V nf
    *)
    fun worldifyGoal (G, V, W as T.Worlds cids, occ) =
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val b = I.targetFam V (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val Wb = W.getWorlds b (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val Rb = worldsToReg Wb (* GEN END TAG OUTSIDE LET *)
        in
          (accR ((G, (V, I.id)), Rb, init);
           raise Error' (occ, "World violation"))
        end
        handle Success V' => V'


    (* worldifyClause (G, V, W, occ) = ()
       iff all subgoals in V satisfy world spec W
       Effect: raises Error' (occ', msg) otherwise

       Invariant: G |- V : type, V nf
       occ is occurrence of V in current clause
     *)
     fun (* GEN BEGIN FUN FIRST *) worldifyClause (G, V as I.Root (a, S), W, occ) = V (* GEN END FUN FIRST *)
       | (* GEN BEGIN FUN BRANCH *) worldifyClause (G, I.Pi ((D as I.Dec (x, V1), I.Maybe), V2), W, occ) =
         let
           (* GEN BEGIN TAG OUTSIDE LET *) val _ = print "{" (* GEN END TAG OUTSIDE LET *)
           (* GEN BEGIN TAG OUTSIDE LET *) val W2 = worldifyClause (decEName (G, D), V2, W, P.body occ) (* GEN END TAG OUTSIDE LET *)
           (* GEN BEGIN TAG OUTSIDE LET *) val _ = print "}" (* GEN END TAG OUTSIDE LET *)
       (*         val W1 = worldifyGoal (G, V1, W, P.label occ) *)
         in
           I.Pi ((I.Dec (x, V1 (* W1*)), I.Maybe), W2)
         end (* GEN END FUN BRANCH *)
       | (* GEN BEGIN FUN BRANCH *) worldifyClause (G, I.Pi ((D as I.Dec (x, V1), I.No), V2), W, occ) =
         let
           (* GEN BEGIN TAG OUTSIDE LET *) val W1 = worldifyGoal (G, V1, W, P.label occ) (* GEN END TAG OUTSIDE LET *)
           (* GEN BEGIN TAG OUTSIDE LET *) val W2 = worldifyClause (decEName (G, D), V2, W, P.body occ) (* GEN END TAG OUTSIDE LET *);
         in
           I.Pi ((I.Dec (x, W1), I.No), W2)
         end (* GEN END FUN BRANCH *)


     (* worldcheck W a = ()
       iff all subgoals in all clauses defining a satisfy world spec W
       Effect: raises Error(msg) otherwise, where msg includes location
     *)
     fun worldifyConDec W (c, I.ConDec (s, m, k, status, V, L)) =
         (if !Global.chatter = 4
            then print (Names.qidToString (Names.constQid c) ^ " ")
          else ();
            if !Global.chatter > 4 then Trace.clause c else ();
              (I.ConDec (s, m, k, status, worldifyClause (I.Null, V, W, P.top), L))
              handle Error' (occ, msg) => raise Error (wrapMsg (c, occ, msg)))
       (* by invariant, other cases cannot apply *)

     fun (* GEN BEGIN FUN FIRST *) worldifyBlock (G, nil) = () (* GEN END FUN FIRST *)
       | (* GEN BEGIN FUN BRANCH *) worldifyBlock (G, (D as (I.Dec (_, V))):: L) =
         let
           (* GEN BEGIN TAG OUTSIDE LET *) val a = I.targetFam V (* GEN END TAG OUTSIDE LET *)
           (* GEN BEGIN TAG OUTSIDE LET *) val W' = W.getWorlds a (* GEN END TAG OUTSIDE LET *)
         in
           ( checkClause W' (G, worldifyClause (I.Null, V, W', P.top), P.top)
           ; worldifyBlock (decUName(G, D), L)
           )
         end (* GEN END FUN BRANCH *)

     fun (* GEN BEGIN FUN FIRST *) worldifyBlocks nil = () (* GEN END FUN FIRST *)
       | (* GEN BEGIN FUN BRANCH *) worldifyBlocks (b :: Bs) =
         let
           (* GEN BEGIN TAG OUTSIDE LET *) val _ = worldifyBlocks Bs (* GEN END TAG OUTSIDE LET *)
           (* GEN BEGIN TAG OUTSIDE LET *) val (Gsome, Lblock) = I.constBlock b (* GEN END TAG OUTSIDE LET *)
           (* GEN BEGIN TAG OUTSIDE LET *) val _ = print "|" (* GEN END TAG OUTSIDE LET *)
         in
           worldifyBlock (Gsome, Lblock)
           handle Error' (occ, s) => raise Error (wrapMsgBlock (b, occ, "World not hereditarily closed"))
         end (* GEN END FUN BRANCH *)

     fun worldifyWorld (T.Worlds Bs) = worldifyBlocks Bs

     fun worldify a =
         let
           (* GEN BEGIN TAG OUTSIDE LET *) val W = W.getWorlds a (* GEN END TAG OUTSIDE LET *)
           (* GEN BEGIN TAG OUTSIDE LET *) val _ = print "[?" (* GEN END TAG OUTSIDE LET *)
           (* GEN BEGIN TAG OUTSIDE LET *) val W' = worldifyWorld W (* GEN END TAG OUTSIDE LET *)
           (* GEN BEGIN TAG OUTSIDE LET *) val _ = print ";" (* GEN END TAG OUTSIDE LET *)
           (* GEN BEGIN TAG OUTSIDE LET *) val _ = if !Global.chatter > 3
                     then print ("World checking family " ^ Names.qidToString (Names.constQid a) ^ ":\n")
                   else () (* GEN END TAG OUTSIDE LET *)
           (* GEN BEGIN TAG OUTSIDE LET *) val condecs = map ((* GEN BEGIN FUNCTION EXPRESSION *) fn (I.Const c) => worldifyConDec W (c, I.sgnLookup c) handle Error' (occ, s) => raise Error (wrapMsg (c, occ, s)) (* GEN END FUNCTION EXPRESSION *))
                             (Index.lookup a) (* GEN END TAG OUTSIDE LET *)
           (* GEN BEGIN TAG OUTSIDE LET *) val _ = map ((* GEN BEGIN FUNCTION EXPRESSION *) fn condec => ( print "#"
                                     ; checkConDec W condec) (* GEN END FUNCTION EXPRESSION *)) condecs (* GEN END TAG OUTSIDE LET *)
           (* GEN BEGIN TAG OUTSIDE LET *) val _ = print "]" (* GEN END TAG OUTSIDE LET *)
     
           (* GEN BEGIN TAG OUTSIDE LET *) val _ = if !Global.chatter = 4 then print "\n" else () (* GEN END TAG OUTSIDE LET *)
         in
           condecs
         end


  in
    (* GEN BEGIN TAG OUTSIDE LET *) val worldify = worldify (* GEN END TAG OUTSIDE LET *)
    (* GEN BEGIN TAG OUTSIDE LET *) val worldifyGoal = (* GEN BEGIN FUNCTION EXPRESSION *) fn (G,V) => worldifyGoal (G, V, W.getWorlds (I.targetFam V), P.top) (* GEN END FUNCTION EXPRESSION *) (* GEN END TAG OUTSIDE LET *)
  end

end (* GEN END FUNCTOR DECL *);  (* functor Worldify *)
