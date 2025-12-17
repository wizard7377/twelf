WorldSyn  Global GLOBAL    Whnf WHNF    Index INDEX    Names NAMES    Unify UNIFY    Abstract ABSTRACT    Constraints CONSTRAINTS    Subordinate SUBORDINATE    Print PRINT    Table TABLE   Key Int    Origins ORIGINS    Timers TIMERS     WORLDSYN  struct module module module module exception exception (* copied from terminates/reduces.fun *)
let rec wrapMsg(c,  , occ,  , msg) (match originLookup c with (fileName,  , nONE) -> (fileName ^ ":" ^ msg) (fileName,  , sOME occDec) -> (wrapLoc' (loc (fileName,  , occToRegionDec occDec occ),  , linesInfoLookup (fileName),  , "While checking constant " ^ qidToString (constQid c) ^ ":\n" ^ msg)))type Dlistlet  inlet rec reset() clear worldsTablelet rec insert(cid,  , w) insert worldsTable (cid,  , w)let rec getWorlds(b) (match lookup worldsTable b with nONE -> raise (error ("Family " ^ qidToString (constQid b) ^ " has no worlds declaration")) sOME (wb) -> wb)(* subsumedTable
       For each family a that is world-checked, this
       contains the subordinate families b whose worlds
       subsume that of a modulo subordination
    *)
let  inlet rec subsumedReset() clear subsumedTablelet rec subsumedInsert(cid) insert subsumedTable (cid,  , ())let rec subsumedLookup(cid) (match lookup subsumedTable cid with nONE -> false sOME _ -> true)(* Regular world expressions R
       Invariants:
       If R = (D1,...,Dn)[s] then G |- s : G' and G' |- D1,...,Dn ctx
       If R = r* then r = 1 or r does not accept the empty world
    *)
type Reg(*     | 1                    *)
exception (* signals worldcheck success *)
(* Format a regular world *)
let rec formatRegr (match r with block (g,  , dl) -> formatDecList (g,  , dl)(* Is this correct? - gaw *)
(* Fixed June 3, 2009 -fp,cs *)
 seq (dl,  , s) -> formatDecList' (null,  , (dl,  , s)) star r -> hbox ([string "("; formatReg r; string ")*"]) plus (r1,  , r2) -> hVbox ([string "("; formatReg r1; string ")"; break; string "|"; space; string "("; formatReg r2; string ")"]) one -> string "1")(* Format a subsumption failure judgment
       msg: Prefix for the message
       dl : declaration list
       Rb : regular world
       b : family
       Displays:

         msg for family b:
         G |- dl </: Rb
     *)
let rec formatSubsumpmsg(g,  , dl,  , rb,  , b) hVbox ([string msg; space; string "for family"; space; string ((qidToString (constQid b)) ^ ":"); break; (* F.Newline (), *)
(* Do not print some-variables; reenable if necessary *)
(* June 3, 2009 -fp,cs *)
(* Print.formatCtx(I.Null, G), F.Break, F.String "|-", F.Space, *)
formatDecList (g,  , dl); break; string ("</:"); space; formatReg rb])(* createEVarSub G G' = s

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
let rec noConstraints(g,  , s) (match collectConstraints (collectEVars (g,  , s,  , nil)) with nil -> true _ -> false)(* end from cover.fun *)
(************)
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
let rec wGoalToString((g,  , l),  , seq (piDecs,  , t)) makestring_fmt (hVbox [hVbox (formatDList (g,  , l,  , id)); break; string "<|"; break; hVbox (formatDList (g,  , piDecs,  , t))])(* Declaration list *)
let rec worldToString(g,  , seq (piDecs,  , t)) makestring_fmt (hVbox (formatDList (g,  , piDecs,  , t)))(* Hypotheses *)
let rec hypsToString(g,  , l) makestring_fmt (hVbox (formatDList (g,  , l,  , id)))(* Mismatch between hypothesis and world declaration *)
let rec mismatchToString(g,  , (v1,  , s1),  , (v2,  , s2)) makestring_fmt (hVbox [formatExp (g,  , eClo (v1,  , s1)); break; string "<>"; break; formatExp (g,  , eClo (v2,  , s2))])(***********)
(* Tracing *)
(***********)
module let rec decUName(g,  , d) decl (g,  , decUName (g,  , d))let rec decEName(g,  , d) decl (g,  , decEName (g,  , d))(**************************************)
(* Matching hypotheses against worlds *)
(**************************************)
let rec subGoalToDList(pi ((d,  , _),  , v)) d :: subGoalToDList (v) subGoalToDList(root _) nil(* worldsToReg (Worlds [c1,...,cn]) = R
       W = R, except that R is a regular expression
       with non-empty contextblocks as leaves
    *)
let rec worldsToReg(worlds nil) one worldsToReg(worlds cids) star (worldsToReg' cids) worldsToReg'(cid :: nil) block (constBlock cid) worldsToReg'(cid :: cids) plus (block (constBlock cid),  , worldsToReg' cids)(* init b (G, L) raises Success iff V is empty
       or none of the remaining declarations are relevant to b
       otherwise fails by returning ()
       Initial continuation for world checker

       Invariant: G |- L dlist, L nf
    *)
let rec initb(_,  , nil) (success (); raise (success)) initb(g,  , l as (d1 as dec (_,  , v1)) :: l2) if belowEq (targetFam v1,  , b) then (unmatched (g,  , l); ()) else init b (decUName (g,  , d1),  , l2)(* accR ((G, L), R, k)   raises Success
       iff L = L1,L2 such that R accepts L1
           and k ((G, L1), L2) succeeds
       otherwise fails by returning ()
       Invariant: G |- L dlist, L nf
                  R regular world expression
       trails at choice points to undo EVar instantiations during matching
    *)
let rec accR(gL,  , one,  , b,  , k) k gL accR(gL as (g,  , l),  , block (someDecs,  , piDecs),  , b,  , k) let let  in(* G |- t : someDecs *)
let  in(* if block matches, check for remaining constraints *)
let  in in accR (gL,  , seq (piDecs,  , t),  , b,  , k') accR((g,  , l as (d as dec (_,  , v1)) :: l2),  , l' as seq (b' as dec (_,  , v1') :: l2',  , t),  , b,  , k) if unifiable (g,  , (v1,  , id),  , (v1',  , t)) then accR ((decUName (g,  , d),  , l2),  , seq (l2',  , dot1 t),  , b,  , k) else if belowEq (targetFam v1,  , b) then (* relevant to family b, fail *)
(mismatch (g,  , (v1,  , id),  , (v1',  , t)); ()) else (* not relevant to family b, skip in L *)
accR ((decUName (g,  , d),  , l2),  , seq (b',  , comp (t,  , shift)),  , b,  , k) accR(gL,  , seq (nil,  , t),  , b,  , k) k gL accR(gL as (g,  , nil),  , r as seq (l',  , t),  , b,  , k) (missing (g,  , r); ()) accR(gL,  , plus (r1,  , r2),  , b,  , k) (trail (fun () -> accR (gL,  , r1,  , b,  , k)); accR (gL,  , r2,  , b,  , k)) accR(gL,  , star (one),  , b,  , k) k gL accR(gL,  , r as star (r'),  , b,  , k) (trail (fun () -> k gL); accR (gL,  , r',  , b,  , fun gL' -> accR (gL',  , r,  , b,  , k)))(* checkSubsumedBlock (G, someDecs, piDecs, Rb, b) = ()
       iff block SOME someDecs. PI piDecs is subsumed by Rb
       Effect: raises Error (msg) otherwise

       Invariants: Rb = reg (worlds (b))
    *)
let rec checkSubsumedBlock(g,  , l',  , rb,  , b) (try  with )(* checkSubsumedWorlds (Wa, Rb, b) = ()
       iff Wa is subsumed by Rb
       Effect: raises Error (msg) otherwise

       Invariants: Rb = reg (worlds (b))
    *)
let rec checkSubsumedWorlds(nil,  , rb,  , b) () checkSubsumedWorlds(cid :: cids,  , rb,  , b) let let  in in checkSubsumedBlock (ctxName (someDecs),  , piDecs,  , rb,  , b)checkSubsumedWorlds (cids,  , rb,  , b)(* checkBlocks W (G, V, occ) = ()
       iff V = {{G'}} a @ S and G' satisfies worlds W
       Effect: raises Error'(occ, msg) otherwise

       Invariants: G |- V : type, V nf
    *)
let rec checkBlocks(worlds cids)(g,  , v,  , occ) try  with (******************************)
(* Checking clauses and goals *)
(******************************)
(* checkClause (G, V, W, occ) = ()
       iff all subgoals in V satisfy world spec W
       Effect: raises Error' (occ', msg) otherwise

       Invariant: G |- V : type, V nf
       occ is occurrence of V in current clause
     *)
let rec checkClause(g,  , root (a,  , s),  , w,  , occ) () checkClause(g,  , pi ((d as dec (_,  , v1),  , maybe),  , v2),  , w,  , occ) (checkClause (decEName (g,  , d),  , v2,  , w,  , body occ); checkGoal (g,  , v1,  , w,  , label occ)) checkClause(g,  , pi ((d as dec (_,  , v1),  , no),  , v2),  , w,  , occ) (checkBlocks w (g,  , v1,  , label occ); checkClause (decEName (g,  , d),  , v2,  , w,  , body occ); checkGoal (g,  , v1,  , w,  , label occ))(* checkGoal (G, V, W, occ) = ()
        iff all (embedded) subgoals in V satisfy world spec W
        Effect: raises Error' (occ', msg) otherwise

        Invariant: G |- V : type, V nf
     *)
(* Question: should dependent Pi's really be checked recursively? *)
(* Thu Mar 29 09:38:20 2001 -fp *)
 checkGoal(g,  , root (a,  , s),  , w,  , occ) () checkGoal(g,  , pi ((d as dec (_,  , v1),  , _),  , v2),  , w,  , occ) (checkGoal (decUName (g,  , d),  , v2,  , w,  , body occ); checkClause (g,  , v1,  , w,  , label occ))(* worldcheck W a = ()
       iff all subgoals in all clauses defining a satisfy world spec W
       Effect: raises Error(msg) otherwise, where msg includes location
    *)
let rec worldcheckwa let let  inlet  in(* initialize table of subsumed families *)
let rec checkAllnil () checkAll(const (c) :: clist) (if ! chatter = 4 then print (qidToString (constQid c) ^ " ") else (); if ! chatter > 4 then clause c else (); try  with ; checkAll clist) checkAll(def (d) :: clist) (if ! chatter = 4 then print (qidToString (constQid d) ^ " ") else (); if ! chatter > 4 then clause d else (); try  with ; checkAll clist)let  inlet  in in ()(**************************)
(* Checking Subordination *)
(**************************)
(*
       At present, worlds declarations must respect the
       current subordination relation in order to guarantee
       soundness.
    *)
let rec ctxAppend(g,  , null) g ctxAppend(g,  , decl (g',  , d)) decl (ctxAppend (g,  , g'),  , d)(* checkSubordBlock (G, G', L') = ()
       Effect: raises Error(msg) if subordination is not respected
               in context block SOME G'. PI L'
       Invariants: G |- SOME G'. PI L' block
    *)
let rec checkSubordBlock(g,  , g',  , l) checkSubordBlock' (ctxAppend (g,  , g'),  , l) checkSubordBlock'(g,  , (d as dec (_,  , v)) :: l') (respectsN (g,  , v); (* is V nf?  Assume here: yes! *)
checkSubordBlock' (decl (g,  , d),  , l')) checkSubordBlock'(g,  , nil) ()(* conDecBlock (condec) = (Gsome, Lpi)
       if condec is a block declaration
       raise Error (msg) otherwise
    *)
let rec conDecBlock(blockDec (_,  , _,  , gsome,  , lpi)) (gsome,  , lpi) conDecBlockcondec raise (error ("Identifier " ^ conDecName condec ^ " is not a block label"))(* constBlock cid = (someDecs, piDecs)
       if cid is defined as a context block
       Effect: raise Error (msg) otherwise
    *)
let rec constBlock(cid) conDecBlock (sgnLookup cid)(* checkSubordWorlds (W) = ()
       Effect: raises Error(msg) if subordination is not respected
               in some context block in W
    *)
let rec checkSubordWorlds(nil) () checkSubordWorlds(cid :: cids) let let  in in checkSubordBlock (null,  , someDecs,  , piDecs)checkSubordWorlds cids(* install (a, W) = ()
       install worlds declaration W for family a

       Effect: raises Error if W does not respect subordination
    *)
let rec install(a,  , w as worlds (cids)) (try  with ; insert (a,  , w))let rec uninstalla match lookup worldsTable a with nONE -> false sOME _ -> (delete worldsTable a; true)(* lookup (a) = SOME W if worlds declared for a, NONE otherwise *)
let rec lookupa getWorlds a(* ctxToList G = L

       Invariant:
       G = L  (G is left associative, L is right associative)
    *)
let rec ctxToList(gin) let let rec ctxToList'(null,  , g) g ctxToList'(decl (g,  , d),  , g') ctxToList' (g,  , d :: g') in ctxToList' (gin,  , nil)(* isSubsumed (W, b) = ()
       holds if the worlds associated with b are subsumed by W
       Effect: raises Error'(occ, msg) otherwise

       Invariants: G |- V : type, V nf
    *)
let rec isSubsumed(worlds cids)b let let  inlet  in in if subsumedLookup b then () else (checkSubsumedWorlds (cids,  , rb,  , b); subsumedInsert (b))let  inlet  inlet  inlet  inlet  inlet  inlet  inlet  inend