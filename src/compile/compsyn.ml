CompSyn  Global GLOBAL    Names NAMES    Table TABLE   Key Int     COMPSYN  struct (*! structure IntSyn = IntSyn' !*)
type Optlet  intype Goal(*     | all x:A. g           *)
 ResGoal(*     | exists' x:_. r       *)
(* exists' is used for local evars
                                           which are introduced to linearize
                                           the head of a clause;
                                           they do not have a type -bp *)
 AuxGoal(* Static programs -- compiled version for substitution trees *)
type Conjunctiontype CompHead(* proof skeletons instead of proof term *)
type Flattermtype Pskeleton(* Representation invariants for compiled syntax:
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
type ConDec(* Other declarations are ignored          *)
(* Static programs --- compiled version of the signature (indexed by first argument) *)
type ConDecDirect(* Other declarations are ignored          *)
(* Compiled Declarations *)
(* added Thu Jun 13 13:41:32 EDT 2002 -cs *)
type ComDec(* The dynamic clause pool --- compiled version of the context *)
(* Dynamic programs: context with synchronous clause pool *)
type DProglet  in(* program array indexed by clause names (no direct head access) *)
let  inlet  in(* Invariants *)
(* 0 <= cid < I.sgnSize () *)
(* program array indexed by clause names (no direct head access) *)
let rec sProgInstall(cid,  , conDec) update (sProgArray,  , cid,  , conDec)let rec sProgLookup(cid) sub (sProgArray,  , cid)let rec sProgReset() modify (fun _ -> void) sProgArraylet  inlet rec detTableCheck(cid) (match (lookup detTable cid) with sOME (deterministic) -> deterministic nONE -> false)let rec detTableReset() clear detTable(* goalSub (g, s) = g'

     Invariants:
     If   G  |- s : G'    G' |- g : A
     then g' = g[s]
     and  G  |- g' : A
  *)
let rec goalSub(atom (p),  , s) atom (eClo (p,  , s)) goalSub(impl (d,  , a,  , ha,  , g),  , s) impl (resGoalSub (d,  , s),  , eClo (a,  , s),  , ha,  , goalSub (g,  , dot1 s)) goalSub(all (d,  , g),  , s) all (decSub (d,  , s),  , goalSub (g,  , dot1 s))(* resGoalSub (r, s) = r'

     Invariants:
     If   G  |- s : G'    G' |- r : A
     then r' = r[s]
     and  G  |- r' : A [s]
  *)
 resGoalSub(eq (q),  , s) eq (eClo (q,  , s)) resGoalSub(and (r,  , a,  , g),  , s) and (resGoalSub (r,  , dot1 s),  , eClo (a,  , s),  , goalSub (g,  , s)) resGoalSub(in (r,  , a,  , g),  , s) in (resGoalSub (r,  , dot1 s),  , eClo (a,  , s),  , goalSub (g,  , s)) resGoalSub(exists (d,  , r),  , s) exists (decSub (d,  , s),  , resGoalSub (r,  , dot1 s))let rec pskeletonToString[] " " pskeletonToString((pc i) :: o) qidToString (constQid i) ^ " " ^ (pskeletonToString o) pskeletonToString((dc i) :: o) ("(Dc " ^ (toString i) ^ ") ") ^ (pskeletonToString o) pskeletonToString(csolver u :: o) ("(cs _ ) " ^ (pskeletonToString o))end   module