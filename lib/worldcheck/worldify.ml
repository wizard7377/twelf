(* Worldification and World-checking *)
(* Author: Carsten Schuermann *)
(* Modified: Frank Pfenning *)

module Worldify
  (Global : GLOBAL)
   (*! (IntSyn : INTSYN) !*)
   (*! (Tomega : TOMEGA) !*)
   (*! sharing Tomega.IntSyn = IntSyn !*)
   (WorldSyn : WORLDSYN)
   (*! sharing WorldSyn.IntSyn = IntSyn !*)
   (*! sharing WorldSyn.Tomega = Tomega !*)
   (Whnf : WHNF)
   (*! sharing Whnf.IntSyn = IntSyn !*)
   (Index : INDEX)
   (*! sharing Index.IntSyn = IntSyn !*)
   (Names : NAMES)
   (*! sharing Names.IntSyn = IntSyn !*)
   (Unify : UNIFY)
   (*! sharing Unify.IntSyn = IntSyn !*)
   (Abstract : ABSTRACT)
   (*! sharing Abstract.IntSyn = IntSyn !*)
   (Constraints : CONSTRAINTS)
   (*! sharing Constraints.IntSyn = IntSyn !*)
   (CSManager : CS_MANAGER)
   (*! sharing CSManager.IntSyn = IntSyn !*)
   (Subordinate : SUBORDINATE)
   (*! sharing Subordinate.IntSyn = IntSyn !*)
   (Print : PRINT)
   (*! sharing Print.IntSyn = IntSyn !*)

   (Table : TABLE with type key = int)
   (MemoTable : TABLE with type key = int * int)
   (IntSet : INTSET)

   (*! (Paths : PATHS) !*)
   (Origins : ORIGINS)
   (*! sharing Origins.Paths = Paths !*)
   (*! sharing Origins.IntSyn = IntSyn !*)
       ): WORLDIFY =
struct
  (*! module IntSyn = IntSyn !*)
  (*! module Tomega = Tomega !*)
  module I = IntSyn
  module T = Tomega
  module P = Paths
  module F = Print.Formatter

  exception Error of string

  exception Error' of P.occ * string

  (* copied from terminates/reduces.fun *)
  let rec wrapMsg (c, occ, msg) =
      (case Origins.originLookup c
         of (fileName, NONE) => (fileName ^ ":" ^ msg)
          | (fileName, SOME occDec) =>
                (P.wrapLoc' (P.Loc (fileName, P.occToRegionDec occDec occ),
                             Origins.linesInfoLookup (fileName),
                             "Constant " ^ Names.qidToString (Names.constQid c) ^ ":" ^ msg)))

  let rec wrapMsgBlock (c, occ, msg) =
      (case Origins.originLookup c
         of (fileName, NONE) => (fileName ^ ":" ^ msg)
          | (fileName, SOME occDec) =>
                (P.wrapLoc' (P.Loc (fileName, P.occToRegionDec occDec occ),
                             Origins.linesInfoLookup (fileName),
                             "Block " ^ Names.qidToString (Names.constQid c) ^ ":" ^ msg)))


  type dlist = IntSyn.dec list


  local
    module W = WorldSyn

    (* Regular world expressions R
       Invariants:
       If R = (D1,...,Dn)[s] then G |- s : G' and G' |- D1,...,Dn ctx
       If R = r* then r = 1 or r does not accept the empty world
    *)
    type reg                        (* Regular world expressions  *)
      = Block of I.cid * (I.dctx * dlist)               (* R ::= LD                   *)
      | Seq of int * dlist * I.Sub      (*     | (Di,...,Dn)[s]       *)
      | Star of reg                     (*     | R*                   *)
      | Plus of reg * reg               (*     | R1 + R2              *)
      | One                             (*     | 1                    *)

    exception Success of I.Exp                  (* signals worldcheck success *)

    (* createEVarSub G G' = s

       Invariant:
       If   G is a context
       and  G' is a context
       then G |- s : G'
    *)
    let rec createEVarSub = function (G, I.Null) -> I.Shift (I.ctxLength G)
      | (G, I.Decl(G', D as I.Dec (_, V))) -> 
        let
          let s = createEVarSub (G, G')
          let V' = I.EClo (V, s)
          let X = I.newEVar (G, V')
        in
          I.Dot (I.Exp X, s)
        end

    (* from cover.fun *)
    (* collectConstraints (Xs) = constrs
       collect all the constraints that may be attached to EVars in Xs

       try simplifying away the constraints in case they are "hard"
    *)
    let rec collectConstraints = function (nil) -> nil
      | (I.EVar (_, _, _, ref nil)::Xs) -> 
          collectConstraints Xs
      | (I.EVar (_, _, _, ref constrs)::Xs) -> 
          (* constrs <> nil *)
          Constraints.simplify constrs @ collectConstraints Xs

    (* collectEVars (G, s, Xs) = Xs'
       adds all uninstantiated EVars from s to Xs to obtain Xs'
       Invariant: s is EVar substitutions
    *)
    let rec collectEVars = function (G, I.Dot (I.Exp X, s), Xs) -> 
           collectEVars (G, s, Abstract.collectEVars (G, (X, I.id), Xs))
      | (G, I.Shift _, Xs) -> Xs
      (* other cases impossible by invariants since s is EVarSubst *)

    (* noConstraints (G, s) = true iff there are no remaining constraints in s
       Invariants: s is an EVar substitution X1...Xn.^k
    *)
    let rec noConstraints (G, s) =
        (case collectConstraints (collectEVars (G, s, nil))
           of nil => true
            | _ => false)

    (************)
    (* Printing *)
    (************)

    (* Declarations *)
    let rec formatD (G, D) =
          F.Hbox (F.String "{" :: Print.formatDec (G, D) :: F.String "}" :: nil)

    (* Declaration lists *)
    let rec formatDList = function (G, nil, t) -> nil
      | (G, D :: nil, t) -> 
        let
          let D' = I.decSub (D, t)
        in
          formatD (G, D') :: nil (* Names.decUName (G, I.decSub(D, t)) *)
        end
      | (G, D :: L, t) -> 
        let
          let D' = I.decSub (D, t) (* Names.decUName (G, I.decSub (D, t)) *)
        in
          formatD (G, D') :: F.Break
          :: formatDList (I.Decl (G, D'), L, I.dot1 t)
        end

    (*
    let rec hypsToDList = function (I.Root _) -> nil
      | (I.Pi ((D, _), V)) -> 
          D::hypsToDList V
    *)

    (* Hypotheses and declaration lists *)
    let rec wGoalToString ((G, L), Seq (_, piDecs, t)) =
        F.makestring_fmt (F.HVbox [F.HVbox (formatDList (G, L, I.id)), F.Break,
                                   F.String "<|", F.Break,
                                   F.HVbox (formatDList (G, piDecs, t))])

    (* Declaration list *)
    let rec worldToString (G, Seq (_, piDecs, t)) =
          F.makestring_fmt (F.HVbox (formatDList (G, piDecs, t)))

    (* Hypotheses *)
    let rec hypsToString (G, L) =
          F.makestring_fmt (F.HVbox (formatDList (G, L, I.id)))

    (* Mismatch between hypothesis and world declaration *)
    let rec mismatchToString (G, (V1, s1), (V2, s2)) =
        F.makestring_fmt (F.HVbox [Print.formatExp (G, I.EClo (V1, s1)), F.Break,
                                   F.String "<>", F.Break,
                                   Print.formatExp (G, I.EClo (V2, s2))])

    (***********)
    (* Tracing *)
    (***********)

    module Trace :
    sig
      let clause : I.cid -> unit
      let constraintsRemain : unit -> unit
      let matchBlock : (I.dctx * dlist) * reg -> unit
      let unmatched : I.dctx * dlist -> unit
      let missing : I.dctx * reg -> unit
      let mismatch : I.dctx * I.eclo * I.eclo -> unit
      let success : unit -> unit
    end =
    struct
      let rec clause (c) =
          print ("World checking clause " ^ Names.qidToString (Names.constQid c) ^ "\n")
      let rec constraintsRemain () =
          if !Global.chatter > 7
            then print ("Constraints remain after matching hypotheses against context block\n")
          else ()
      let rec matchBlock (GL, R) =          (* R = (D1,...,Dn)[t] *)
          if !Global.chatter > 7
            then print ("Matching:\n" ^ wGoalToString (GL, R) ^ "\n")
          else ()
      let rec unmatched GL =
          if !Global.chatter > 7
            then print ("Unmatched hypotheses:\n" ^ hypsToString GL ^ "\n")
          else ()
      let rec missing (G, R) =              (* R = (D1,...,Dn)[t] *)
          if !Global.chatter > 7
            then print ("Missing hypotheses:\n" ^ worldToString (G, R) ^ "\n")
          else ()
      let rec mismatch (G, Vs1, Vs2) =
          if !Global.chatter > 7
            then print ("Mismatch:\n" ^ mismatchToString (G, Vs1, Vs2) ^ "\n")
          else ()
      let rec success () =
          if !Global.chatter > 7
            then print ("Success\n")
          else ()
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
     let rec equivList = function (G, (_, nil), nil) -> true
       | (G, (t, I.Dec (_, V1) :: L1), I.Dec (_, V2) :: L2) -> 
           (( Unify.unify (G, (V1, t), (V2, I.id))
            ; equivList (G, (I.dot1 t, L1), L2)
            ) handle Unify.Unify _ => false)
       | _ -> false


     (* equivBlock ((G, L), L') = B

        Invariant:
        If   G |- L block
        then B = true if there exists a substitution . |- t : G, s.t. L[t] = L'
             B = false otherwise
     *)
     let rec equivBlock ((G, L), L') =
         let
           let t = createEVarSub (I.Null, G)
         in
           equivList (I.Null, (t, L), L')
         end

     (* equivBlocks W L = B

        Invariant:
        Let W be a world and L be a block.
        B = true if exists L' in W such that L = L'
        B = false otherwise
     *)
     let rec equivBlocks = function W1 nil -> true
       | nil L' -> false
       | (b :: W1) L' -> 
           equivBlock (I.constBlock b, L')
           orelse equivBlocks W1 L'

     (* strengthen a (t, L) = L'

        Invariant:
        If   a is a type family,
        and  . |- t : G
        and  G |- L block
        then . |- L' block
        where V \in L and not V < a then V \in L'
        and   V \in L and V < a then not V \in L'
     *)
     let rec strengthen = function a (t, nil) -> nil
       | a (t, (D as I.Dec (_, V)) :: L) -> 
         if Subordinate.below (I.targetFam V, a) then (I.decSub (D, t) :: strengthen a (I.dot1 t, L))
         else strengthen a (I.Dot (I.Undef,  t), L)


     (* subsumedBlock a W1 (G, L) = ()

        Invariant:
        If   a is a type family
        and  W1 the world in which the callee is defined
        and (G, L) one block in the world of the caller
        Then the function returns () if (G, L) is subsumed by W1
        otherwise Error is raised
     *)
     let rec subsumedBlock a W1 (G, L) =
         let
           let t = createEVarSub (I.Null, G) (* G |- t : someDecs *)
           let L' = strengthen a (t, L)
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
     let rec subsumedBlocks = function a W1 nil -> ()
       | a W1 (b :: W2) -> 
           ( subsumedBlock a W1 (I.constBlock b)
           ; subsumedBlocks a W1 W2
           )

     (* subsumedWorld a W1 W2 = ()

        Invariant:
        Let W1 be the world in which the callee is defined
        Let W2 be the world in which the caller is defined
        Then the function returns () if W2 is subsumed by W1
        otherwise Error is raised
     *)
     let rec subsumedWorld a (T.Worlds W1) (T.Worlds W2) =
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
     let rec eqCtx = function (I.Null, I.Null) -> true
       | (I.Decl (G1, D1), I.Decl (G2, D2)) -> 
           eqCtx (G1, G2) andalso Conv.convDec ((D1, I.id), (D2, I.id))
       | _ -> false

     (* eqList (L1, L2) = B

        Invariant:
        Let  L1, L2 lists of declarations (as the occur in a block).
        B = true if L1 and L2 are equal (modulo renaming of variables)
        B = false otherwise
     *)
     let rec eqList = function (nil, nil) -> true
       | (D1 :: L1, D2 :: L2) -> 
           Conv.convDec ((D1, I.id), (D2, I.id)) andalso eqList (L1, L2)
       | _ -> false


     (* eqBlock (b1, b2) = B

        Invariant:
        Let  b1, b2 blocks.
        B = true if b1 and b2 are equal (modulo renaming of variables)
        B = false otherwise
     *)
     let rec eqBlock (b1, b2) =
         let
           let (G1, L1) = I.constBlock b1
           let (G2, L2) = I.constBlock b2
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
     let rec subsumedCtx = function (I.Null, W) -> ()
       | (I.Decl (G, I.BDec (_, (b, _))), W as T.Worlds Bs) -> 
          ( if List.exists (fn b' => eqBlock (b, b')) Bs
              then () else raise Error "Dynamic world subsumption failed"
          ; subsumedCtx (G, W)
          )
       | (I.Decl (G, _), W as T.Worlds Bs) -> 
          subsumedCtx (G, W)



    (******************************)
    (* Checking clauses and goals *)
    (******************************)

     (* checkGoal W (G, V, occ) = ()
        iff all (embedded) subgoals in V satisfy world spec W
        Effect: raises Error' (occ', msg) otherwise

        Invariant: G |- V : type, V nf
     *)
     let rec checkGoal = function W (G, I.Root (I.Const a, S), occ) -> 
         let
           let W' = W.getWorlds a
         in
           ( subsumedWorld a W' W
           ; subsumedCtx (G, W)
           )
         end
       | W (G, I.Pi ((D, _), V2), occ) -> 
           checkGoal W (decUName (G, D), V2, P.body occ)

    (* checkClause (G, V, W, occ) = ()
       iff all subgoals in V satisfy world spec W
       Effect: raises Error' (occ', msg) otherwise

       Invariant: G |- V : type, V nf
       occ is occurrence of V in current clause
     *)
     let rec checkClause = function W (G, I.Root (a, S), occ) -> ()
       | W (G, I.Pi ((D as I.Dec (_, V1), I.Maybe), V2), occ) -> 
         checkClause W (decEName (G, D), V2, P.body occ)
       | W (G, I.Pi ((D as I.Dec (_, V1), I.No), V2), occ) -> 
         (checkClause W (decEName (G, D), V2, P.body occ);
          checkGoal W (G, V1, P.label occ))

     let rec checkConDec W (I.ConDec (s, m, k, status, V, L)) =
           checkClause W (I.Null, V, P.top)



    (**************************************)
    (* Matching hypotheses against worlds *)
    (**************************************)

    let rec subGoalToDList = function (I.Pi ((D, _), V)) -> D::subGoalToDList(V)
      | (I.Root _) -> nil

    (* worldsToReg (Worlds [c1,...,cn]) = R
       W = R, except that R is a regular expression
       with non-empty contextblocks as leaves
    *)
    let rec worldsToReg = function (T.Worlds nil) -> One
      | (T.Worlds cids) -> Star (worldsToReg' cids)
    and worldsToReg' (cid::nil) = Block (cid, I.constBlock cid)
      | worldsToReg' (cid::cids) =
          Plus (Block (cid, I.constBlock cid), worldsToReg' cids)

    (* init b (G, L) raises Success iff V is empty
       or none of the remaining declarations are relevant to b
       otherwise fails by returning ()
       Initial continuation for world checker

       Invariant: G |- L dlist, L nf
    *)
    let rec init = function (_, Vs as (I.Root _, s)) -> 
        (Trace.success () ;
         raise Success (Whnf.normalize Vs))
      | (G, (V as I.Pi ((D1 as I.Dec (_, V1), _), V2), s)) -> 
        (Trace.unmatched (G, subGoalToDList (Whnf.normalize (V, s))) ; ())

    (* accR ((G, (V, s)), R, k)   raises Success
       iff V[s] = {L1}{L2} P  such that R accepts L1
           and k ((G, L1), L2) succeeds
       otherwise fails by returning ()
       Invariant: G |- (V s) type, L nf
                  R regular world expression
       trails at choice points to undo EVar instantiations during matching
    *)
    let rec accR = function (GVs, One, k) -> k GVs
      | (GVs as (G, (V, s)), Block (c, (someDecs, piDecs)), k) -> 
        let
          let t = createEVarSub (G, someDecs) (* G |- t : someDecs *)
          let _ = Trace.matchBlock ((G, subGoalToDList (Whnf.normalize (V, s))), Seq (1, piDecs, t))
          let k' = (fn (G', Vs') =>
                    if noConstraints (G, t)
                      then k (G', Vs')
                    else (Trace.constraintsRemain (); ()))

        in
          accR ((decUName (G, I.BDec (NONE, (c, t))), (V, I.comp (s, I.shift))),
                Seq (1, piDecs, I.comp (t, I.shift)), k')
          handle Success V => raise Success (Whnf.normalize (I.Pi ((I.BDec (NONE, (c, t)), I.Maybe), V), I.id))
        end
      | accR ((G, (V as I.Pi ((D as I.Dec (_, V1), _), V2), s)),
              L' as Seq (j, I.Dec (_, V1')::L2', t), k) =
        if Unify.unifiable (G, (V1, s), (V1', t))
          then accR ((G, (V2, I.Dot (I.Exp (I.Root (I.Proj (I.Bidx 1, j), I.Nil)), s))),
                     Seq (j+1, L2', I.Dot (I.Exp (I.Root (I.Proj (I.Bidx 1, j), I.Nil)), t)), k)
        else  (Trace.mismatch (G, (V1, I.id), (V1', t)) ; ())
      | (GVs, Seq (_, nil, t), k) -> k GVs
      | (GVs as (G, (I.Root _, s)), R as Seq (_, L', t), k) -> 
          ( Trace.missing (G, R); () )  (* L is missing *)
      | (GVs, Plus (r1, r2), k) -> 
          ( CSManager.trail (fn () => accR (GVs, r1, k)) ;
            accR (GVs, r2, k) )
      | (GVs, Star (One), k) -> k GVs (* only possibility for non-termination in next rule *)
      | (GVs, r as Star(r'), k) -> (* r' does not accept empty declaration list *)
          ( CSManager.trail (fn () => k GVs) ;
            accR (GVs, r', fn GVs' => accR (GVs', r, k)))


    (******************************)
    (* Worldifying clauses and goals *)
    (******************************)

    (* worldifyGoal (G, V, W, occ) = ()
       iff V = {{G'}} a @ S and G' satisfies worlds W
       Effect: raises Error' (occ', msg) otherwise

       Invariant: G |- V : type, V nf
    *)
    let rec worldifyGoal (G, V, W as T.Worlds cids, occ) =
        let
          let b = I.targetFam V
          let Wb = W.getWorlds b
          let Rb = worldsToReg Wb
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
     let rec worldifyClause = function (G, V as I.Root (a, S), W, occ) -> V
       | (G, I.Pi ((D as I.Dec (x, V1), I.Maybe), V2), W, occ) -> 
         let
           let _ = print "{"
           let W2 = worldifyClause (decEName (G, D), V2, W, P.body occ)
           let _ = print "}"
(*         let W1 = worldifyGoal (G, V1, W, P.label occ) *)
         in
           I.Pi ((I.Dec (x, V1 (* W1*)), I.Maybe), W2)
         end
       | worldifyClause (G, I.Pi ((D as I.Dec (x, V1), I.No), V2), W, occ) =
         let
           let W1 = worldifyGoal (G, V1, W, P.label occ)
           let W2 = worldifyClause (decEName (G, D), V2, W, P.body occ);
         in
           I.Pi ((I.Dec (x, W1), I.No), W2)
         end


     (* worldcheck W a = ()
       iff all subgoals in all clauses defining a satisfy world spec W
       Effect: raises Error(msg) otherwise, where msg includes location
     *)
     let rec worldifyConDec W (c, I.ConDec (s, m, k, status, V, L)) =
         (if !Global.chatter = 4
            then print (Names.qidToString (Names.constQid c) ^ " ")
          else ();
            if !Global.chatter > 4 then Trace.clause c else ();
              (I.ConDec (s, m, k, status, worldifyClause (I.Null, V, W, P.top), L))
              handle Error' (occ, msg) => raise Error (wrapMsg (c, occ, msg)))
       (* by invariant, other cases cannot apply *)

     let rec worldifyBlock = function (G, nil) -> ()
       | (G, (D as (I.Dec (_, V))):: L) -> 
         let
           let a = I.targetFam V
           let W' = W.getWorlds a
         in
           ( checkClause W' (G, worldifyClause (I.Null, V, W', P.top), P.top)
           ; worldifyBlock (decUName(G, D), L)
           )
         end

     let rec worldifyBlocks = function nil -> ()
       | (b :: Bs) -> 
         let
           let _ = worldifyBlocks Bs
           let (Gsome, Lblock) = I.constBlock b
           let _ = print "|"
         in
           worldifyBlock (Gsome, Lblock)
           handle Error' (occ, s) => raise Error (wrapMsgBlock (b, occ, "World not hereditarily closed"))
         end

     let rec worldifyWorld (T.Worlds Bs) = worldifyBlocks Bs

     let rec worldify a =
         let
           let W = W.getWorlds a
           let _ = print "[?"
           let W' = worldifyWorld W
           let _ = print ";"
           let _ = if !Global.chatter > 3
                     then print ("World checking family " ^ Names.qidToString (Names.constQid a) ^ ":\n")
                   else ()
           let condecs = map (fn (I.Const c) => worldifyConDec W (c, I.sgnLookup c) handle Error' (occ, s) => raise Error (wrapMsg (c, occ, s)))
                             (Index.lookup a)
           let _ = map (fun condec -> ( print "#"
                                     ; checkConDec W condec)) condecs
           let _ = print "]"

           let _ = if !Global.chatter = 4 then print "\n" else ()
         in
           condecs
         end


  in
    let worldify = worldify
    let worldifyGoal = fn (G,V) => worldifyGoal (G, V, W.getWorlds (I.targetFam V), P.top)
  end

end;; (* functor Worldify *)
