(* Compiled Syntax *)

(* Author: Iliano Cervesato *)

(* Modified: Jeff Polakow *)

(* Modified: Frank Pfenning *)

(* Modified: Brigitte Pientka *)

module CompSyn (Global : GLOBAL) (Names : NAMES) : COMPSYN = struct
  (*! structure IntSyn = IntSyn' !*)

  type opt = No | LinearHeads | Indexing

  let optimize = ref LinearHeads

  type goal =
    | Atom of IntSyn.exp
    | Impl of
        resGoal
        * IntSyn.exp (*     | (r,A,a) => g         *)
        * IntSyn.head
        * goal
    | All of IntSyn.dec * goal

  and resGoal =
    | Eq of IntSyn.exp
    | Assign of IntSyn.exp * auxGoal
    | And of resGoal (*     | r & (A,g)            *) * IntSyn.exp * goal
    | In of resGoal (*     | r && (A,g)           *) * IntSyn.exp * goal
    | Exists of IntSyn.dec * resGoal
    | Axists of IntSyn.dec * resGoal

  and auxGoal =
    | Trivial
    | UnifyEq of
        IntSyn.dctx * IntSyn.exp (* call unify *) * IntSyn.exp * auxGoal
  (* Static programs -- compiled version for_sml substitution trees *)

  type conjunction = True | Conjunct of goal * IntSyn.exp * conjunction

  type compHead =
    | Head of (IntSyn.exp * IntSyn.dec IntSyn.ctx * auxGoal * IntSyn.cid)
  (* proof skeletons instead of proof term *)

  type flatterm = Pc of IntSyn.cid | Dc of IntSyn.cid | Csolver of IntSyn.exp
  type pskeleton = flatterm list
  (* Representation invariants for_sml compiled syntax:
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
        a  target head of A (for_sml indexing purposes)

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

  type conDec = SClause of resGoal | Void
  (* Other declarations are ignored          *)

  (* Static programs --- compiled version of the signature (indexed by first argument) *)

  type conDecDirect = HeadGoals of compHead * conjunction | Null
  (* Other declarations are ignored          *)

  (* Compiled Declarations *)

  (* added Thu Jun 13 13:41:32 EDT 2002 -cs *)

  type comDec =
    | Parameter
    | Dec of resGoal * IntSyn.sub * IntSyn.head
    | BDec of resGoal * IntSyn.sub * IntSyn.head list
    | PDec
  (* The dynamic clause pool --- compiled version of the context *)

  (* Dynamic programs: context with synchronous clause pool *)

  type dProg = DProg of IntSyn.dctx * comDec IntSyn.ctx

  let maxCid = Global.maxCid
  (* program array indexed by clause names (no direct head access) *)

  let sProgArray = (Array.array (maxCid + 1, Void) : conDec Array.array)
  let detTable : bool Table.table = Table.new_ 32
  (* Invariants *)

  (* 0 <= cid < I.sgnSize () *)

  (* program array indexed by clause names (no direct head access) *)

  let rec sProgInstall (cid, conDec) = Array.update (sProgArray, cid, conDec)
  let rec sProgLookup cid = Array.sub (sProgArray, cid)
  let rec sProgReset () = Array.modify (fun _ -> Void) sProgArray
  let detTableInsert = Table.insert detTable

  let rec detTableCheck cid =
    match Table.lookup detTable cid with
    | Some deterministic -> deterministic
    | None -> false

  let rec detTableReset () = Table.clear detTable
  (* goalSub (g, s) = g'

     Invariants:
     If   G  |- s : G'    G' |- g : A
     then g' = g[s]
     and  G  |- g' : A
  *)

  let rec goalSub = function
    | Atom p, s -> Atom (IntSyn.EClo (p, s))
    | Impl (d, A, Ha, g), s ->
        Impl
          (resGoalSub (d, s), IntSyn.EClo (A, s), Ha, goalSub (g, IntSyn.dot1 s))
    | All (D, g), s -> All (IntSyn.decSub (D, s), goalSub (g, IntSyn.dot1 s))

  and resGoalSub = function
    | Eq q, s -> Eq (IntSyn.EClo (q, s))
    | And (r, A, g), s ->
        And (resGoalSub (r, IntSyn.dot1 s), IntSyn.EClo (A, s), goalSub (g, s))
    | In (r, A, g), s ->
        In (resGoalSub (r, IntSyn.dot1 s), IntSyn.EClo (A, s), goalSub (g, s))
    | Exists (D, r), s ->
        Exists (IntSyn.decSub (D, s), resGoalSub (r, IntSyn.dot1 s))

  let rec pskeletonToString = function
    | [] -> " "
    | Pc i :: O ->
        Names.qidToString (Names.constQid i) ^ " " ^ pskeletonToString O
    | Dc i :: O -> ("(Dc " ^ Int.toString i ^ ") ") ^ pskeletonToString O
    | Csolver U :: O -> "(cs _ ) " ^ pskeletonToString O
end

(* functor CompSyn *)

module CompSyn =
  CompSyn
    (struct
      module Global = Global
    end)
    (struct
      module Names = Names
    end)
    (struct
      module Table = IntRedBlackTree
    end)
(* Compiled Syntax *)

(* Author: Iliano Cervesato *)

(* Modified: Jeff Polakow *)

module type COMPSYN = sig
  (*! structure IntSyn : INTSYN !*)
  type opt = No | LinearHeads | Indexing

  val optimize : opt ref

  type goal =
    | Atom of IntSyn.exp
    | Impl of
        resGoal
        * IntSyn.exp (*     | (r,A,a) => g         *)
        * IntSyn.head
        * goal
    | All of IntSyn.dec * goal

  and resGoal =
    | Eq of IntSyn.exp
    | Assign of IntSyn.exp * auxGoal
    | And of resGoal (*     | r & (A,g)            *) * IntSyn.exp * goal
    | In of resGoal (*     | r virt& (A,g)        *) * IntSyn.exp * goal
    | Exists of IntSyn.dec * resGoal
    | Axists of IntSyn.dec * resGoal

  and auxGoal =
    | Trivial
    | UnifyEq of
        IntSyn.dctx * IntSyn.exp (* call unify *) * IntSyn.exp * auxGoal

  (* Static programs -- compiled version for_sml substitution trees *)
  type conjunction = True | Conjunct of goal * IntSyn.exp * conjunction

  type compHead =
    | Head of (IntSyn.exp * IntSyn.dec IntSyn.ctx * auxGoal * IntSyn.cid)

  (* pskeleton instead of proof term *)
  type flatterm = Pc of int | Dc of int | Csolver of IntSyn.exp
  type pskeleton = flatterm list

  (* The dynamic clause pool --- compiled version of the context *)
  (* type dpool = (ResGoal * IntSyn.Sub * IntSyn.cid) option IntSyn.Ctx *)
  (* Compiled Declarations *)
  (* added Thu Jun 13 13:41:32 EDT 2002 -cs *)
  type comDec =
    | Parameter
    | Dec of resGoal * IntSyn.sub * IntSyn.head
    | BDec of resGoal * IntSyn.sub * IntSyn.head list
    | PDec

  (* Dynamic programs: context with synchronous clause pool *)
  type dProg = DProg of (IntSyn.dctx * comDec IntSyn.ctx)

  (* Programs --- compiled version of the signature (no direct head access) *)
  type conDec = SClause of resGoal | Void

  (* Other declarations are ignored  *)
  (* Install Programs (without indexing) *)
  val sProgInstall : IntSyn.cid * conDec -> unit
  val sProgLookup : IntSyn.cid -> conDec
  val sProgReset : unit -> unit

  (* Deterministic flag *)
  val detTableInsert : IntSyn.cid * bool -> unit
  val detTableCheck : IntSyn.cid -> bool
  val detTableReset : unit -> unit

  (* Explicit Substitutions *)
  val goalSub : goal * IntSyn.sub -> goal
  val resGoalSub : resGoal * IntSyn.sub -> resGoal
  val pskeletonToString : pskeleton -> string
end

(* signature COMPSYN *)
