(* Compiled Syntax *)
(* Author: Iliano Cervesato *)
(* Modified: Jeff Polakow *)
(* Modified: Frank Pfenning *)
(* Modified: Brigitte Pientka *)

functor CompSyn (structure Global : GLOBAL
                 (*! structure IntSyn' : INTSYN !*)
                 structure Names : NAMES
                 (*! sharing Names.IntSyn = IntSyn' !*)
                 structure Table : TABLE
                   where type key = int)
  : COMPSYN =
struct

  (*! structure IntSyn = IntSyn' !*)


  datatype opt = No | LinearHeads | Indexing

  val optimize = ref LinearHeads

  datatype goal =                       (* Goals                      *)
    Atom of IntSyn.exp                  (* g ::= p                    *)
  | Impl of res_goal * IntSyn.exp        (*     | (r,A,a) => g         *)
            * IntSyn.head * goal
  | All  of IntSyn.dec * goal           (*     | all x:A. g           *)

  and res_goal =                         (* Residual Goals             *)
    Eq     of IntSyn.exp                (* r ::= p = ?                *)
  | Assign of IntSyn.exp * aux_goal      (*     | p = ?, where p has   *)
                                        (* only new vars,             *)
                                        (* then unify all the vars    *)
  | And    of res_goal                   (*     | r & (A,g)            *)
              * IntSyn.exp * goal
  | In     of res_goal                   (*     | r && (A,g)           *)
              * IntSyn.exp * goal
  | Exists of IntSyn.dec * res_goal      (*     | exists x:A. r        *)
  | Axists of IntSyn.dec * res_goal      (*     | exists' x:_. r       *)
                                        (* exists' is used for local evars
                                           which are introduced to linearize
                                           the head of a clause;
                                           they do not have a type -bp *)

  and aux_goal =
    Trivial                               (* trivially done *)
  | UnifyEq of IntSyn.dctx * IntSyn.exp   (* call unify *)
             * IntSyn.exp * aux_goal

  (* Static programs -- compiled version for substitution trees *)
  datatype conjunction = True | Conjunct of goal * IntSyn.exp * conjunction

  datatype comp_head =
     Head of (IntSyn.exp * IntSyn.dec IntSyn.ctx * aux_goal * IntSyn.cid)


  (* proof skeletons instead of proof term *)
  datatype flatterm =
    Pc of IntSyn.cid | Dc of IntSyn.cid | Csolver of IntSyn.exp

  type pskeleton = flatterm list

  (* Representation invariants for compiled syntax:
     Judgments:
       G |- g goal   g is a valid goal in G
       G |- r resgoal  g is a valid residual goal in G

       G |- A ~> g   A compiles to goal g
       G |- A ~> r   A compiles to residual goal r
       G |- A ~> <head , subgoals>

     G |- p  goal
     if  G |- p : type, p = H @ S       (* mod whnf *)

     G |- (r, A, a) => g  goal
     if G |- A : type
        G |- r  resgoal
        G |- A ~> r
        a  target head of A (for indexing purposes)

     G |- all x:A. g  goal
     if G |- A : type
        G, x:A |- g  goal

     For dynamic clauses:

     G |- q  resgoal
     if G |- q : type, q = H @ S        (* mod whnf *)

     G |- r & (A,g)  resgoal
     if G |- A : type
        G |- g  goal
        G |- A ~> g
        G, _:A |- r  resgoal

     G |- exists x:A. r  resgoal
     if  G |- A : type
         G, x:A |- r  resgoal

     G |- exists' x:A. r  resgoal     but exists' doesn't effect the proof-term
     if  G |- A : type
         G, x:A |- r  resgoal

     For static clauses:
     G |- true subgoals

     if G |- sg && g subgoals
     if G |- g goal
        G |- sg subgoals

  *)

  (* Static programs --- compiled version of the signature (no indexing) *)
  datatype con_dec =                        (* Compiled constant declaration           *)
       SClause of res_goal                  (* c : A  -- static clause (residual goal) *)
    | Void                                 (* Other declarations are ignored          *)

  (* Static programs --- compiled version of the signature (indexed by first argument) *)
  datatype con_dec_direct =                  (* Compiled constant declaration     *)
      HeadGoals of comp_head * conjunction  (* static clause with direct head access   *)
    | Null                                 (* Other declarations are ignored          *)

  (* Compiled Declarations *)
  (* added Thu Jun 13 13:41:32 EDT 2002 -cs *)
  datatype com_dec =
    Parameter
  | Dec of res_goal * IntSyn.sub * IntSyn.head
  | BDec of (res_goal * IntSyn.sub *IntSyn.head) list
  | PDec

  (* The dynamic clause pool --- compiled version of the context *)
  (* Dynamic programs: context with synchronous clause pool *)

  datatype d_prog = DProg of IntSyn.dctx * com_dec IntSyn.ctx

  local
    val maxCid = Global.maxCid
    (* program array indexed by clause names (no direct head access) *)
    val sProgArray = Array.array (maxCid+1, Void) : con_dec Array.array

    val detTable : bool Table.table = Table.new (32)
  in
    (* Invariants *)
    (* 0 <= cid < I.sgnSize () *)
    (* program array indexed by clause names (no direct head access) *)
    fun sProgInstall (cid, conDec) = Array.update (sProgArray, cid, conDec)

    fun sProgLookup (cid) = Array.sub (sProgArray, cid)
    fun sProgReset () = Array.modify (fn _ => Void) sProgArray

    val detTableInsert = Table.insert detTable;
    fun detTableCheck (cid) = (case (Table.lookup detTable cid)
                                 of SOME(deterministic) => deterministic
                                  | NONE => false)
    fun detTableReset () = Table.clear detTable;
  end
  (* goalSub (g, s) = g'

     Invariants:
     If   G  |- s : G'    G' |- g : A
     then g' = g[s]
     and  G  |- g' : A
  *)
  fun goalSub (Atom(p), s) = Atom(IntSyn.EClo(p,s))
    | (* GEN CASE BRANCH *) goalSub (Impl(d, A, Ha, g), s) =
       Impl (resGoalSub (d, s), IntSyn.EClo(A, s), Ha,
             goalSub (g, IntSyn.dot1 s))
    | (* GEN CASE BRANCH *) goalSub (All(D, g), s) =
       All (IntSyn.decSub(D,s), goalSub (g, IntSyn.dot1 s))

  (* resGoalSub (r, s) = r'

     Invariants:
     If   G  |- s : G'    G' |- r : A
     then r' = r[s]
     and  G  |- r' : A [s]
  *)
  and resGoalSub (Eq(q), s) = Eq (IntSyn.EClo (q,s))
    | (* GEN CASE BRANCH *) resGoalSub (And(r, A, g), s) =
        And (resGoalSub (r, IntSyn.dot1 s), IntSyn.EClo(A,s), goalSub (g, s))
    | (* GEN CASE BRANCH *) resGoalSub (In(r, A, g), s) =
        In (resGoalSub (r, IntSyn.dot1 s), IntSyn.EClo(A,s), goalSub (g, s))
    | (* GEN CASE BRANCH *) resGoalSub (Exists(D, r), s) =
        Exists (IntSyn.decSub(D, s), resGoalSub (r, IntSyn.dot1 s))


  fun pskeletonToString [] = " "
    | (* GEN CASE BRANCH *) pskeletonToString ((Pc i)::O) =
        Names.qidToString (Names.constQid i) ^ " " ^ (pskeletonToString O)
    | (* GEN CASE BRANCH *) pskeletonToString ((Dc i)::O) =
        ("(Dc " ^ (Int.toString i) ^ ") ") ^ (pskeletonToString O)
    | (* GEN CASE BRANCH *) pskeletonToString (Csolver U ::O) =
        ("(cs _ ) " ^ (pskeletonToString O))


end;  (* functor CompSyn *)

structure CompSyn =
  CompSyn (structure Global = Global
           (*! structure IntSyn' = IntSyn !*)
           structure Names = Names
           structure Table = IntRedBlackTree);

