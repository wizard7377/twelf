Worldify  Global GLOBAL    WorldSyn WORLDSYN    Whnf WHNF    Index INDEX    Names NAMES    Unify UNIFY    Abstract ABSTRACT    Constraints CONSTRAINTS    CSManager CS_MANAGER    Subordinate SUBORDINATE    Print PRINT    Table TABLE   Key Int    MemoTable TABLE   Key Int * Int    IntSet INTSET    Origins ORIGINS     WORLDIFY  struct (*! structure IntSyn = IntSyn !*)
(*! structure Tomega = Tomega !*)
module module module module exception exception (* copied from terminates/reduces.fun *)
let rec wrapMsg(c,  , occ,  , msg) (match originLookup c with (fileName,  , nONE) -> (fileName ^ ":" ^ msg) (fileName,  , sOME occDec) -> (wrapLoc' (loc (fileName,  , occToRegionDec occDec occ),  , linesInfoLookup (fileName),  , "Constant " ^ qidToString (constQid c) ^ ":" ^ msg)))let rec wrapMsgBlock(c,  , occ,  , msg) (match originLookup c with (fileName,  , nONE) -> (fileName ^ ":" ^ msg) (fileName,  , sOME occDec) -> (wrapLoc' (loc (fileName,  , occToRegionDec occDec occ),  , linesInfoLookup (fileName),  , "Block " ^ qidToString (constQid c) ^ ":" ^ msg)))type Dlistmodule (* Regular world expressions R
       Invariants:
       If R = (D1,...,Dn)[s] then G |- s : G' and G' |- D1,...,Dn ctx
       If R = r* then r = 1 or r does not accept the empty world
    *)
type Reg(*     | 1                    *)
exception (* signals worldcheck success *)
(* createEVarSub G G' = s

       Invariant:
       If   G is a context
       and  G' is a context
       then G |- s : G'
    *)
let rec createEVarSub(g,  , null) shift (ctxLength g) createEVarSub(g,  , decl (g',  , d as dec (_,  , v))) let let  inlet  inlet  in in dot (exp x,  , s)(* from cover.fun *)
(* collectConstraints (Xs) = constrs
       collect all the constraints that may be attached to EVars in Xs

       try simplifying away the constraints in case they are "hard"
    *)
let rec collectConstraints(nil) nil collectConstraints(eVar (_,  , _,  , _,  , ref nil) :: xs) collectConstraints xs collectConstraints(eVar (_,  , _,  , _,  , ref constrs) :: xs) simplify constrs @ collectConstraints xs(* collectEVars (G, s, Xs) = Xs'
       adds all uninstantiated EVars from s to Xs to obtain Xs'
       Invariant: s is EVar substitutions
    *)
let rec collectEVars(g,  , dot (exp x,  , s),  , xs) collectEVars (g,  , s,  , collectEVars (g,  , (x,  , id),  , xs)) collectEVars(g,  , shift _,  , xs) xs(* other cases impossible by invariants since s is EVarSubst *)
(* noConstraints (G, s) = true iff there are no remaining constraints in s
       Invariants: s is an EVar substitution X1...Xn.^k
    *)
let rec noConstraints(g,  , s) (match collectConstraints (collectEVars (g,  , s,  , nil)) with nil -> true _ -> false)(************)
(* Printing *)
(************)
(* Declarations *)
let rec formatD(g,  , d) hbox (string "{" :: formatDec (g,  , d) :: string "}" :: nil)(* Declaration lists *)
let rec formatDList(g,  , nil,  , t) nil formatDList(g,  , d :: nil,  , t) let let  in in formatD (g,  , d') :: nil(* Names.decUName (G, I.decSub(D, t)) *)
 formatDList(g,  , d :: l,  , t) let let  in(* Names.decUName (G, I.decSub (D, t)) *)
 in formatD (g,  , d') :: break :: formatDList (decl (g,  , d'),  , l,  , dot1 t)(*
    fun hypsToDList (I.Root _) = nil
      | hypsToDList (I.Pi ((D, _), V)) =
          D::hypsToDList V
    *)
(* Hypotheses and declaration lists *)
let rec wGoalToString((g,  , l),  , seq (_,  , piDecs,  , t)) makestring_fmt (hVbox [hVbox (formatDList (g,  , l,  , id)); break; string "<|"; break; hVbox (formatDList (g,  , piDecs,  , t))])(* Declaration list *)
let rec worldToString(g,  , seq (_,  , piDecs,  , t)) makestring_fmt (hVbox (formatDList (g,  , piDecs,  , t)))(* Hypotheses *)
let rec hypsToString(g,  , l) makestring_fmt (hVbox (formatDList (g,  , l,  , id)))(* Mismatch between hypothesis and world declaration *)
let rec mismatchToString(g,  , (v1,  , s1),  , (v2,  , s2)) makestring_fmt (hVbox [formatExp (g,  , eClo (v1,  , s1)); break; string "<>"; break; formatExp (g,  , eClo (v2,  , s2))])(***********)
(* Tracing *)
(***********)
module let rec decUName(g,  , d) decl (g,  , decUName (g,  , d))let rec decEName(g,  , d) decl (g,  , decEName (g,  , d))(* ******************** *)
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
let rec equivList(g,  , (_,  , nil),  , nil) true equivList(g,  , (t,  , dec (_,  , v1) :: l1),  , dec (_,  , v2) :: l2) (try  with ) equivList_ false(* equivBlock ((G, L), L') = B

        Invariant:
        If   G |- L block
        then B = true if there exists a substitution . |- t : G, s.t. L[t] = L'
             B = false otherwise
     *)
let rec equivBlock((g,  , l),  , l') let let  in in equivList (null,  , (t,  , l),  , l')(* equivBlocks W L = B

        Invariant:
        Let W be a world and L be a block.
        B = true if exists L' in W such that L = L'
        B = false otherwise
     *)
let rec equivBlocksw1nil true equivBlocksnill' false equivBlocks(b :: w1)l' equivBlock (constBlock b,  , l') || equivBlocks w1 l'(* strengthen a (t, L) = L'

        Invariant:
        If   a is a type family,
        and  . |- t : G
        and  G |- L block
        then . |- L' block
        where V \in L and not V < a then V \in L'
        and   V \in L and V < a then not V \in L'
     *)
let rec strengthena(t,  , nil) nil strengthena(t,  , (d as dec (_,  , v)) :: l) if below (targetFam v,  , a) then (decSub (d,  , t) :: strengthen a (dot1 t,  , l)) else strengthen a (dot (undef,  , t),  , l)(* subsumedBlock a W1 (G, L) = ()

        Invariant:
        If   a is a type family
        and  W1 the world in which the callee is defined
        and (G, L) one block in the world of the caller
        Then the function returns () if (G, L) is subsumed by W1
        otherwise Error is raised
     *)
let rec subsumedBlockaw1(g,  , l) let let  in(* G |- t : someDecs *)
let  in in if equivBlocks w1 l' then () else raise (error "Static world subsumption failed")(* subsumedBlocks a W1 W2 = ()

        Invariant:
        Let W1 be the world in which the callee is defined
        Let W2 be the world in which the caller is defined
        Then the function returns () if W2 is subsumed by W1
        otherwise Error is raised
     *)
let rec subsumedBlocksaw1nil () subsumedBlocksaw1(b :: w2) (subsumedBlock a w1 (constBlock b); subsumedBlocks a w1 w2)(* subsumedWorld a W1 W2 = ()

        Invariant:
        Let W1 be the world in which the callee is defined
        Let W2 be the world in which the caller is defined
        Then the function returns () if W2 is subsumed by W1
        otherwise Error is raised
     *)
let rec subsumedWorlda(worlds w1)(worlds w2) subsumedBlocks a w1 w2(* ******************** *)
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
let rec eqCtx(null,  , null) true eqCtx(decl (g1,  , d1),  , decl (g2,  , d2)) eqCtx (g1,  , g2) && convDec ((d1,  , id),  , (d2,  , id)) eqCtx_ false(* eqList (L1, L2) = B

        Invariant:
        Let  L1, L2 lists of declarations (as the occur in a block).
        B = true if L1 and L2 are equal (modulo renaming of variables)
        B = false otherwise
     *)
let rec eqList(nil,  , nil) true eqList(d1 :: l1,  , d2 :: l2) convDec ((d1,  , id),  , (d2,  , id)) && eqList (l1,  , l2) eqList_ false(* eqBlock (b1, b2) = B

        Invariant:
        Let  b1, b2 blocks.
        B = true if b1 and b2 are equal (modulo renaming of variables)
        B = false otherwise
     *)
let rec eqBlock(b1,  , b2) let let  inlet  in in eqCtx (g1,  , g2) && eqList (l1,  , l2)(* sumbsumedCtx (G, W) = ()

        Invariant:
        Let G be a context of blocks
        and W a world
        Then the function returns () if every block in G
        is listed in W
        otherwise Error is raised
     *)
let rec subsumedCtx(null,  , w) () subsumedCtx(decl (g,  , bDec (_,  , (b,  , _))),  , w as worlds bs) (if exists (fun b' -> eqBlock (b,  , b')) bs then () else raise (error "Dynamic world subsumption failed"); subsumedCtx (g,  , w)) subsumedCtx(decl (g,  , _),  , w as worlds bs) subsumedCtx (g,  , w)(******************************)
(* Checking clauses and goals *)
(******************************)
(* checkGoal W (G, V, occ) = ()
        iff all (embedded) subgoals in V satisfy world spec W
        Effect: raises Error' (occ', msg) otherwise

        Invariant: G |- V : type, V nf
     *)
let rec checkGoalw(g,  , root (const a,  , s),  , occ) let let  in in (subsumedWorld a w' w; subsumedCtx (g,  , w)) checkGoalw(g,  , pi ((d,  , _),  , v2),  , occ) checkGoal w (decUName (g,  , d),  , v2,  , body occ)(* checkClause (G, V, W, occ) = ()
       iff all subgoals in V satisfy world spec W
       Effect: raises Error' (occ', msg) otherwise

       Invariant: G |- V : type, V nf
       occ is occurrence of V in current clause
     *)
let rec checkClausew(g,  , root (a,  , s),  , occ) () checkClausew(g,  , pi ((d as dec (_,  , v1),  , maybe),  , v2),  , occ) checkClause w (decEName (g,  , d),  , v2,  , body occ) checkClausew(g,  , pi ((d as dec (_,  , v1),  , no),  , v2),  , occ) (checkClause w (decEName (g,  , d),  , v2,  , body occ); checkGoal w (g,  , v1,  , label occ))let rec checkConDecw(conDec (s,  , m,  , k,  , status,  , v,  , l)) checkClause w (null,  , v,  , top)(**************************************)
(* Matching hypotheses against worlds *)
(**************************************)
let rec subGoalToDList(pi ((d,  , _),  , v)) d :: subGoalToDList (v) subGoalToDList(root _) nil(* worldsToReg (Worlds [c1,...,cn]) = R
       W = R, except that R is a regular expression
       with non-empty contextblocks as leaves
    *)
let rec worldsToReg(worlds nil) one worldsToReg(worlds cids) star (worldsToReg' cids) worldsToReg'(cid :: nil) block (cid,  , constBlock cid) worldsToReg'(cid :: cids) plus (block (cid,  , constBlock cid),  , worldsToReg' cids)(* init b (G, L) raises Success iff V is empty
       or none of the remaining declarations are relevant to b
       otherwise fails by returning ()
       Initial continuation for world checker

       Invariant: G |- L dlist, L nf
    *)
let rec init(_,  , vs as (root _,  , s)) (success (); raise (success (normalize vs))) init(g,  , (v as pi ((d1 as dec (_,  , v1),  , _),  , v2),  , s)) (unmatched (g,  , subGoalToDList (normalize (v,  , s))); ())(* accR ((G, (V, s)), R, k)   raises Success
       iff V[s] = {L1}{L2} P  such that R accepts L1
           and k ((G, L1), L2) succeeds
       otherwise fails by returning ()
       Invariant: G |- (V s) type, L nf
                  R regular world expression
       trails at choice points to undo EVar instantiations during matching
    *)
let rec accR(gVs,  , one,  , k) k gVs accR(gVs as (g,  , (v,  , s)),  , block (c,  , (someDecs,  , piDecs)),  , k) let let  in(* G |- t : someDecs *)
let  inlet  in in try  with  accR((g,  , (v as pi ((d as dec (_,  , v1),  , _),  , v2),  , s)),  , l' as seq (j,  , dec (_,  , v1') :: l2',  , t),  , k) if unifiable (g,  , (v1,  , s),  , (v1',  , t)) then accR ((g,  , (v2,  , dot (exp (root (proj (bidx 1,  , j),  , nil)),  , s))),  , seq (j + 1,  , l2',  , dot (exp (root (proj (bidx 1,  , j),  , nil)),  , t)),  , k) else (mismatch (g,  , (v1,  , id),  , (v1',  , t)); ()) accR(gVs,  , seq (_,  , nil,  , t),  , k) k gVs accR(gVs as (g,  , (root _,  , s)),  , r as seq (_,  , l',  , t),  , k) (missing (g,  , r); ()) accR(gVs,  , plus (r1,  , r2),  , k) (trail (fun () -> accR (gVs,  , r1,  , k)); accR (gVs,  , r2,  , k)) accR(gVs,  , star (one),  , k) k gVs accR(gVs,  , r as star (r'),  , k) (trail (fun () -> k gVs); accR (gVs,  , r',  , fun gVs' -> accR (gVs',  , r,  , k)))(******************************)
(* Worldifying clauses and goals *)
(******************************)
(* worldifyGoal (G, V, W, occ) = ()
       iff V = {{G'}} a @ S and G' satisfies worlds W
       Effect: raises Error' (occ', msg) otherwise

       Invariant: G |- V : type, V nf
    *)
let rec worldifyGoal(g,  , v,  , w as worlds cids,  , occ) try  with (* worldifyClause (G, V, W, occ) = ()
       iff all subgoals in V satisfy world spec W
       Effect: raises Error' (occ', msg) otherwise

       Invariant: G |- V : type, V nf
       occ is occurrence of V in current clause
     *)
let rec worldifyClause(g,  , v as root (a,  , s),  , w,  , occ) v worldifyClause(g,  , pi ((d as dec (x,  , v1),  , maybe),  , v2),  , w,  , occ) let let  inlet  inlet  in(*         val W1 = worldifyGoal (G, V1, W, P.label occ) *)
 in pi ((dec (x,  , v1, (* W1*)
),  , maybe),  , w2) worldifyClause(g,  , pi ((d as dec (x,  , v1),  , no),  , v2),  , w,  , occ) let let  inlet  in in pi ((dec (x,  , w1),  , no),  , w2)(* worldcheck W a = ()
       iff all subgoals in all clauses defining a satisfy world spec W
       Effect: raises Error(msg) otherwise, where msg includes location
     *)
let rec worldifyConDecw(c,  , conDec (s,  , m,  , k,  , status,  , v,  , l)) (if ! chatter = 4 then print (qidToString (constQid c) ^ " ") else (); if ! chatter > 4 then clause c else (); try  with )(* by invariant, other cases cannot apply *)
let rec worldifyBlock(g,  , nil) () worldifyBlock(g,  , (d as (dec (_,  , v))) :: l) let let  inlet  in in (checkClause w' (g,  , worldifyClause (null,  , v,  , w',  , top),  , top); worldifyBlock (decUName (g,  , d),  , l))let rec worldifyBlocksnil () worldifyBlocks(b :: bs) let let  inlet  inlet  in in try  with let rec worldifyWorld(worlds bs) worldifyBlocks bslet rec worldifya let let  inlet  inlet  inlet  inlet  inlet  inlet  inlet  inlet  in in condecslet  inlet  inend