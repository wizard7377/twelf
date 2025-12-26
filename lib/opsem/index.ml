open Basis ;; 
(* Indexing *)

(* Author: Brigitte Pientka *)

module type TABLEINDEX = sig
  (*! structure IntSyn : Intsyn.INTSYN !*)
  (*! structure CompSyn : Compsyn.COMPSYN !*)
  type answer =
    < solutions : (IntSyn.dctx * IntSyn.sub) * CompSyn.pskeleton list
    ; lookup : int >

  type strategy = Variant | Subsumption

  val strategy : strategy ref
  val termDepth : int option ref
  val ctxDepth : int option ref
  val ctxLength : int option ref
  val strengthen : bool ref

  val query :
    IntSyn.dctx
    * IntSyn.dctx
    * IntSyn.exp
    * IntSyn.sub
    * (CompSyn.pskeleton -> unit) option ref

  type answState = New | Repeated

  (* table: G, Gdprog |- goal , 
            (answ list (ith stage) , answ list (1 to i-1 th stage))
   *)
  val table :
    (int ref * IntSyn.dctx * IntSyn.dctx * IntSyn.exp) * answer list ref

  val noAnswers : (IntSyn.dctx * IntSyn.dctx * IntSyn.exp) * answer list -> bool

  (* call check/insert *)
  (* callCheck (G, D, U)
   *
   * if D, G |- U     in table  
   *    then SOME(entries)
   * if D, G |- U not in table 
   *    then NONE  
   *          SIDE EFFECT: D, G |- U added to table
   *)
  val callCheck :
    IntSyn.dctx * IntSyn.dctx * IntSyn.exp ->
    (IntSyn.dctx * IntSyn.dctx * IntSyn.exp) * answer list option

  (* answer check/insert *)
  (* answerCheck (G, D, (U,s))
   * 
   * Assumption: D, G |- U is in table
   *             and A represents the corresponding solutions
   * 
   * G |- s : D, G
   * Dk, G |- sk : D, G
   *
   * If  (Dk, sk) in A then repeated
   *  else New
   *)
  val answerCheck :
    IntSyn.dctx * IntSyn.dctx * IntSyn.exp * IntSyn.sub * CompSyn.pskeleton ->
    answState

  (* reset table *)
  val reset : unit -> unit
  val printTable : unit -> unit
  val printTableEntries : unit -> unit

  (* updateTable 
   *
   * SIDE EFFECT: 
   *   for_sml each table entry: 
   *       advance lookup pointer
   *
   * if Table did not change during last stage 
   *    then updateTable () =  false
   * else updateTable () = true
   *)
  val updateTable : unit -> bool
  val solutions : answer -> (IntSyn.dctx * IntSyn.sub) * CompSyn.pskeleton list
  val lookup : answer -> int
end

(* signature Table.TABLEINDEX *)
(* Indexing for_sml table *)


(* Author: Brigitte Pientka *)


module TableIndex (Global : Global.GLOBAL) (Queue : Queue.QUEUE) (Subordinate : Subordinate.SUBORDINATE) (Conv : Conv.CONV) (Unify : Unify.UNIFY) (AbstractTabled : Abstract.Abstract.ABSTRACTTABLED) (Whnf : Whnf.WHNF) (Print : Print.PRINT) (CPrint : Cprint.CPRINT) (Names : Names.NAMES) (TypeCheck : Typecheck.TYPECHECK) : Table.TABLEINDEX = struct (*! structure IntSyn = IntSyn' !*)

(*! structure CompSyn = CompSyn' !*)

module Conv = Conv
(* Table.TABLE

   table entry : D, G  |- u

   Answer substitution:

                 Dk, G  |- sk : D, G

   Answer :
                 Dk, G |- u[sk]
   *)

(* solution: (Dk, sk)

   * lookup  : pointer to the i-th element in solution list
   *)

type answer = <solutions: (IntSyn.dctx * IntSyn.sub) * CompSyn.pskeleton list; lookup: int>
(* entry = (((i, G, D, U), A)) where i is the access counter
   *)

type entry = (((int ref * IntSyn.dctx * IntSyn.dctx * IntSyn.exp) * answer))
type entries = entry list
type index = entry list
type answState = New | Repeated
type strategy = Variant | Subsumption
let added = ref false
(* ---------------------------------------------------------------------- *)

(* global search parameters *)

let strategy = ref Variant
(* Subsumption *)

(* Variant *)

(* term abstraction after term depth is Greater than 5 *)

let termDepth = (ref None : int option ref)
let ctxDepth = (ref None : int option ref)
let ctxLength = (ref None : int option ref)
(*   val termDepth = ref (!globalTermDepth); *)

(*   val ctxDepth = ref (!globalCtxDepth);   *)

(*   val ctxLength = ref (!globalCtxLength); *)

(* apply strengthening during abstraction *)

let strengthen = AbstractTabled.strengthen
(* original query *)

let query : IntSyn.dctx * IntSyn.dctx * IntSyn.exp * IntSyn.sub * (CompSyn.pskeleton -> unit) option ref = ref None
(* ---------------------------------------------------------------------- *)

module I = IntSyn
module C = CompSyn
module A = AbstractTabled
(* Global Table *)

let table : index ref = ref []
(* concat(Gdp, G) = G''
     *
     * if Gdp = ym...y1
     *    G   = xn...x1
     * then
     *    Gdp, G = G''
     *    ym...y1, xn...x1
     *
     *)

let rec concat = function (I.Null, G') -> G' | (I.Decl (G, D), G') -> I.Decl (concat (G, G'), D)
let rec reverse = function (I.Null, G') -> G' | (I.Decl (G, D), G') -> reverse (G, I.Decl (G', D))
(* ---------------------------------------------------------------------- *)

(* printTable () = () *)

let rec printTable ()  = ( let rec proofTerms = function (G, D, U, []) -> print "" | (G, D, U, (((D', s'), _) :: S)) -> ((* (print (Print.expToString (I.Null,  *)
(*              A.raiseType(Names.ctxName(concat(G,D')), I.EClo(U, s')))) *)
(try print (Print.expToString (I.Null, A.raiseType (Names.ctxName (D'), I.EClo (A.raiseType (Names.ctxName (G), U), s')))) with _ -> print "EXCEPTION"); (* do not print pskeletons *)
print ", \n\t"; proofTerms (G, D, U, S)) in let rec printT = function [] -> () | (((k, G, D, U), {solutions = S; lookup = i}) :: T) -> match S with [] -> (printT T; print (Print.expToString (I.Null, A.raiseType (concat (G, D), U)) ^ ", NONE\n")) | (a :: answ) -> (printT T; print (Print.expToString (I.Null, A.raiseType (concat (G, D), U)) ^ ", [\n\t"); proofTerms (G, D, U, (rev S)); print (" ] -- lookup : " ^ Int.toString i ^ "\n\n")) in  print ("Table: \n"); printT (! table); print ("End Table \n"); print ("Number of table entries   : " ^ Int.toString (length (! table)) ^ "\n") )
(* printTableEntries () = () *)

let rec printTableEntries ()  = ( let rec printT = function [] -> () | (((k, G, D, U), {solutions = S; lookup = i}) :: T) -> (printT T; print (Print.expToString (I.Null, A.raiseType (concat (G, D), U)) ^ "\n Access Counter : " ^ (Int.toString (! k)) ^ " \n")) in  print ("TableEntries: \n"); printT (! table); print ("End TableEntries \n"); print ("Number of table entries   : " ^ Int.toString (length (! table)) ^ "\n") )
(* ---------------------------------------------------------------------- *)

(* Term Abstraction *)

let rec lengthSpine = function (I.Nil) -> 0 | (I.SClo (S, s')) -> 1 + lengthSpine (S)
let rec exceedsTermDepth (i)  = match (! termDepth) with None -> false | Some (n) -> (i > n)
let rec exceedsCtxDepth (i)  = match (! ctxDepth) with None -> false | Some (n) -> (print ("\n exceedsCtxDepth " ^ Int.toString i ^ " > " ^ Int.toString n ^ " ? "); (i > n))
let rec exceedsCtxLength (i)  = match (! ctxLength) with None -> false | Some (n) -> (i > n)
let rec max (x, y)  = if x > y then x else y
let rec oroption = function (None, None, None) -> false | (Some (k), _, _) -> true | (_, Some (n), _) -> true | (_, _, Some (n)) -> true
let rec abstractionSet ()  = oroption (! termDepth, ! ctxDepth, ! ctxLength)
(* countDepth U =
         ctr = (ctrTerm, ctrDecl, ctrLength)
         ctrTerm : max term depth
         ctrDecl : max type depth in decl
         ctrLength : length of decl

    *)

let rec exceeds (U)  = countDecl (0, 0, U)
and countDecl = function (ctrType, ctrLength, I.Pi ((D, _), V)) -> ( (*         val _ = print ("\n ctrType' = " ^ Int.toString ctrType')  *)
let ctrType' = countDec (0, D) in  if ctrType' > ctrType then countDecl (ctrType', ctrLength + 1, V) else countDecl (ctrType, ctrLength + 1, V) ) | (ctrType, ctrLength, U) -> ( (*         val _ = print ("\n 1 ctrTerm = " ^ Int.toString ctrTerm)
           val _ = print ("\n 1 ctxLength = " ^ Int.toString ctrLength)
           val _ = print ("\n 1 ctxDepth = " ^ Int.toString ctrType)
*)
let ctrTerm = count (0, U) in  exceedsCtxDepth (ctrType) || exceedsCtxLength (ctrLength) || exceedsTermDepth (count (0, U)) )
and countDec = function (ctr, I.Dec (_, U)) -> count (ctr, U) | (ctr, I.BDec (_, s)) -> 0
and count = function (ctr, (U)) -> ctr | (ctr, I.Pi ((D, _), V)) -> ( (*         val _ = print ("\n ctrTerm = " ^ Int.toString ctrTerm)
           val _ = print ("\n ctrType = " ^ Int.toString ctrType)
*)
let ctrTerm = count (ctr, V) in let ctrType = countDec (ctr, D) in  max (ctrType, ctrTerm)(* to revise ?*)
 ) | (ctr, I.Root (F, S)) -> ( (*         val _ = print ("\n spineDepth = " ^ Int.toString ctrDepth)
           val _ = print ("\n RootF = " ^ Int.toString(ctrDepth + ctr))
*)
let ctrDepth = countSpine (1, S) in  (ctrDepth + 1 + ctr)(*         (ctrLength + ctr) *)
 ) | (ctr, I.Redex (U, S)) -> ( (*         val _ = print ("\n SpindeDepth = " ^ Int.toString ctrDepth)
           val _ = print ("\n Redex = " ^ Int.toString(max(ctrDepth',ctrDepth) + ctr))*)
let ctrDepth = count (0, U) in let ctrDepth' = countSpine (ctrDepth, S) in  (max (ctrDepth', ctrDepth) + ctr) ) | (ctr, I.Lam (D, U)) -> count (ctr + 1, U) | (ctr, (X)) -> ctr | (ctr, I.EClo (E, s)) -> count (ctr, E) | (ctr, (F)) -> (ctr)
and countSpine = function (ctrDepth, I.Nil) -> ctrDepth | (ctr, I.SClo (S, s')) -> countSpine (ctr, S) | (ctrDepth, I.App (U, S)) -> ( let ctrDepth' = count (0, U) in  countSpine (max (ctrDepth', ctrDepth), S) )
(* ---------------------------------------------------------------------- *)

(* reinstSub (G, D, s) = s'
    *
    * If D', G |- s : D, G
    * then  G |- s' : D, G
    *)

let rec reinstSub = function (G, I.Null, s) -> s | (G, I.Decl (D, I.Dec (_, A)), s) -> ( let X = I.newEVar (I.Null, A) in  I.Dot (I.Exp (X), reinstSub (G, D, s)) )
(* ---------------------------------------------------------------------- *)

(* variant (U,s) (U',s')) = bool   *)

let rec variant (Us, Us')  = Conv.conv (Us, Us')
(* subsumes ((G, D, U), (G', D', U')) = bool
     *
     * if
     *    D, G   |- U
     *    D', G' |- U'
     * then
     *      G' |- s' : D', G'
     *    return true if D, G |- U is an instance of G' |- U'[s']
     *    otherwise false
     *
     *)

let rec subsumes ((G, D, U), (G', D', U'))  = ( let Upi = A.raiseType (G, U) in let Upi' = A.raiseType (G', U') in let s' = reinstSub (G', D', I.id) in  Cs.CSManager.trail (fun () -> Unify.unifiable (D, (Upi', s'), (Upi, I.id))) )
let rec equalSub = function (I.Shift k, I.Shift k') -> (k = k') | (I.Dot (F, S), I.Dot (F', S')) -> equalFront (F, F') && equalSub (S, S') | (I.Dot (F, S), I.Shift k) -> false | (I.Shift k, I.Dot (F, S)) -> false
and equalFront = function (I.Idx n, I.Idx n') -> (n = n') | (I.Exp U, I.Exp V) -> Conv.conv ((U, I.id), (V, I.id)) | (I.Undef, I.Undef) -> true
let rec equalSub1 (I.Dot (ms, s), I.Dot (ms', s'))  = equalSub (s, s')
let rec equalCtx = function (I.Null, I.Null) -> true | (I.Decl (Dk, I.Dec (_, A)), I.Decl (D1, I.Dec (_, A1))) -> Conv.conv ((A, I.id), (A1, I.id)) && equalCtx (Dk, D1)
(* ---------------------------------------------------------------------- *)

(* Call check and insert *)

(* callCheck (G, D, U) = callState

       check whether D, G |- U is in the table

     returns NONE,
        if D, G |- U is not already in the table
          Sideeffect: add D, G |- U to table

     returns SOME(A)
        if D, G |- U is in table and
          A is an entry in the table together with its answer list

    Variant:
    if it succeeds there is exactly one table entry which is a variant to U
    Subsumption:
    if it succeeds it will return the most general table entry of which U is
    an instance of (by invariant now, the most general table entry will be found first,
    any entry found later, will be an instance of this entry)
    *)

let rec callCheckVariant (G, D, U)  = ( let Upi = A.raiseType (concat (G, D), U) in let rec lookup = function ((G, D, U), []) -> (table := ((ref 1, G, D, U), {solutions = []; lookup = 0}) :: (! table); (if (! Global.chatter) >= 5 then (print ("\n \n Added "); print (Print.expToString (I.Null, Upi) ^ "\n to Table \n")) else ()); added := true; (* if termdepth(U) > n then force the tabled engine to suspend
               * and treat it like it is already in the table, but no answ available *)
if abstractionSet () then ((* print ("\n term " ^ Print.expToString (I.Null, Upi) ^
                  " exceeds depth or length ? \n"); *)
if exceeds (A.raiseType (G, U)) then ((if (! Global.chatter) >= 5 then print ("\n term " ^ Print.expToString (I.Null, Upi) ^ " exceeds depth or length \n") else ()); Some ([])) else None) else None) | ((G, D, U), ((H) :: T)) -> if variant ((Upi, I.id), (A.raiseType (concat (G', D'), U'), I.id)) then (k := ! k + 1; (if (! Global.chatter) >= 5 then print ("call " ^ Print.expToString (I.Null, Upi) ^ " found in table \n ") else ()); Some [((G', D', U'), answ)]) else lookup ((G, D, U), T) in  lookup ((G, D, U), (! table)) )
(* Subsumption:

       Assumes: Table is in order [tn, ...., t1]
       i.e. tn is added to the table later than t1
            this implies that tn is more general than ti (i < n)

       if we find a tn s.t M is an instance of it, then return tn
       and do not search further

    *)

let rec callCheckSubsumes (G, D, U)  = ( let rec lookup = function ((G, D, U), []) -> (table := ((ref 1, G, D, U), {solutions = []; lookup = 0}) :: (! table); (if (! Global.chatter) >= 5 then print ("Added " ^ Print.expToString (I.Null, A.raiseType (concat (G, D), U)) ^ " to Table \n") else ()); added := true; if exceeds (A.raiseType (G, U)) then ((if (! Global.chatter) >= 4 then print ("\n term " ^ Print.expToString (I.Null, A.raiseType (concat (G, D), U)) ^ " exceeds depth or length \n") else ()); Some ([])) else None) | ((G, D, U), (((k, G', D', U'), answ) :: T)) -> if (subsumes ((G, D, U), (G', D', U'))) then ((if (! Global.chatter) >= 5 then print ("call " ^ Print.expToString (I.Null, A.raiseType (concat (G, D), U)) ^ "found in table \n ") else ()); k := ! k + 1; Some ([((G', D', U'), answ)])) else lookup ((G, D, U), T) in  lookup ((G, D, U), (! table)) )
(* ---------------------------------------------------------------------- *)

let rec member = function ((Dk, sk), []) -> false | ((Dk, sk), (((D1, s1), _) :: S)) -> if equalSub (sk, s1) && equalCtx (Dk, D1) then true else member ((Dk, sk), S)
(* answer check and insert

      if     G |- U[s]
          D, G |- U
             G |- s : D, G

      answerCheck (G, D, (U,s)) = repeated
         if s already occurs in answer list for_sml U
      answerCheck (G, D, (U,s)) = new
         if s did not occur in answer list for_sml U
         Sideeffect: update answer list for_sml U

        Dk, G |- sk : D, G
        Dk, G |- U[sk]

        sk is the abstraction of s and Dk contains all "free" vars

     *)

let rec answCheckVariant (G, D, U, s, O)  = ( let Upi = A.raiseType (concat (G, D), U) in let _ = if (! Global.chatter) >= 5 then (print "\n AnswCheckInsert: "; print (Print.expToString (I.Null, I.EClo (A.raiseType (G, U), s)) ^ "\n"); print "\n Table Index : "; print (Print.expToString (I.Null, Upi) ^ "\n")) else () in let rec lookup = function ((G, D, U, s), [], T) -> (print (Print.expToString (I.Null, I.EClo (A.raiseType (G, U), s)) ^ " call should always be already in the table !\n"); Repeated) | ((G, D, U, s), ((H) :: T), T') -> if variant ((Upi, I.id), (A.raiseType (concat (G', D'), U'), I.id)) then ( let (Dk, sk) = A.abstractAnswSub s in  (* answer check *)
if member ((Dk, sk), S) then Repeated else (table := (rev T') @ (((k, G', D', U'), {solutions = (((Dk, sk), O) :: S); lookup = i}) :: T); (if (! Global.chatter) >= 5 then (print ("\n Add solution  -- "); print (Print.expToString (I.Null, I.EClo (A.raiseType (G', U'), s))); print ("\n solution added  -- "); print (Print.expToString (I.Null, A.raiseType (Names.ctxName (Dk), I.EClo (A.raiseType (G', U'), sk))))) else ()); New) ) else lookup (G, D, U, s) T (H :: T') in  lookup (G, D, U, s) (! table) [] )
(* memberSubsumes ((G, Dk, U, sk), (G', U', A)) = bool

   If Dk, G |- U[sk]

      A = ((Dn, sn), On), ....., ((D1, s1), O1)

      for_sml all i in [1, ..., n]
          Di, G' |- U'[si]
              G' |- si' : Di, G'
   then
     exists an i in [1,...,n]  s.t.
         Dk, G |- U[sk] is an instance of G' |- U'[si']
   *)

let rec memberSubsumes = function ((G, D, U, s), (G', U', [])) -> false | ((G, D, U, s), (G', U', (((D1, s1), _) :: A))) -> ( (* assume G' and G are the same for_sml now *)
let Upi = A.raiseType (G, U) in let Upi' = A.raiseType (G', U') in let s1' = reinstSub (G', D1, I.id) in let Vpis = (I.EClo (Upi', s1), s1') in let b = Cs.CSManager.trail (fun () -> Unify.unifiable (D, (Upi, s), (Vpis))) in  if b then ((if (! Global.chatter) >= 5 then print "\n answer in table subsumes answer \n " else ()); true) else memberSubsumes ((G, D, U, s), (G', U', A)) )
let rec shift = function (0, s) -> s | (n, s) -> shift (n - 1, I.dot1 s)
let rec answCheckSubsumes (G, D, U, s, O)  = ( let Upi = A.raiseType (G, U) in let _ = if (! Global.chatter) >= 4 then (print ("\n AnswCheckInsert (subsumes): "); print (Print.expToString (I.Null, I.EClo (Upi, s)) ^ "\n")) else () in let rec lookup = function ((G, D, U, s), [], T) -> (print (Print.expToString (concat (G, D), I.EClo (U, s)) ^ " call should always be already in the table !\n"); Repeated) | ((G, D, U, s), (((k, G', D', U'), {solutions = A; lookup = i}) :: T), T') -> if (subsumes ((G, D, U), (G', D', U'))) then ( let (Dk, sk) = A.abstractAnswSub s in  if memberSubsumes ((G, Dk, U, sk), (G', U', A)) then Repeated else ( (*  higher-order matching *)
(* reinstantiate us' *)
let s' = reinstSub (G', D', I.id) in let _ = if (! Global.chatter) >= 4 then (print "\n new answer to be added to Index \n"; print (Print.expToString (I.Null, A.raiseType (concat (G', D'), U')) ^ "\n"); print "\n answer added \n"; print (Print.expToString (I.Null, A.raiseType (Dk, I.EClo (A.raiseType (G, U), sk))) ^ "\n")) else () in let _ = if (Unify.unifiable (Dk, (A.raiseType (G, U), sk), (A.raiseType (G', U'), s'))) then (if (! Global.chatter) >= 4 then (print "\n1 unification successful !\n"; print (Print.expToString (I.Null, A.raiseType (Dk, I.EClo (A.raiseType (G', U'), s'))) ^ "\n")) else ()) else print "\n1 unification failed! -- should never happen ?" in let (Dk', sk') = A.abstractAnsw (Dk, s') in let rs = reinstSub (G', Dk', I.id) in  (match ! query with None -> ()(* nothing to do *)
 | Some (G1, D1, U1, s1, sc1) -> ((if (! Global.chatter) >= 4 then (print ("Generate answers for_sml: "); print (Print.expToString (I.Null, I.EClo (A.raiseType (G1, U1), s1)) ^ " \n"); print ("Answer in table: "); print (Print.expToString (I.Null, A.raiseType (Dk, I.EClo (A.raiseType (G', U'), s'))) ^ " : \n"); print (Print.expToString (I.Null, I.EClo (A.raiseType (Dk, I.EClo (A.raiseType (G', U'), sk')), rs)) ^ " : \n")) else ()); (if (subsumes ((G1, D1, U1), (G', D', U'))) then (* original query is an instance of the entry we are adding answ to *)
Cs.CSManager.trail (fun () -> (if Unify.unifiable (D1, (A.raiseType (G1, U1), s1), (I.EClo (A.raiseType (G', U'), sk'), rs)) then ( let w = if (! strengthen) then Subordinate.weaken (I.Null, IntSyn.targetFam (I.EClo (U1, s1))) else I.id in  (* (I.EClo(N1, I.comp(shift(I.ctxLength(Gdp1),s1), w))) *)
sc1 O ) else ())) else ()))); table := ((rev T') @ (((k, G', D', U'), {solutions = (((Dk', sk'), O) :: A); lookup = i}) :: T)); (if (! Global.chatter) >= 5 then (print ("\n \n solution (original) was: \n"); print (Print.expToString (I.Null, I.EClo (A.raiseType (G, U), s)) ^ "\n"); print ("\n \n solution (deref) was: \n"); print (Print.expToString (I.Null, A.raiseType (Dk, I.EClo (A.raiseType (G, U), sk))) (*                    print(Print.expToString(I.Null, I.EClo(A.raiseType(concat(G, Dk), U), sk)) *)
 ^ "\n"); print ("\n solution added  --- "); print (Print.expToString (I.Null, A.raiseType (Dk', I.EClo (A.raiseType (G', U'), s'))) ^ "\n"); print ("\n solution added (dereferenced) --- "); print (Print.expToString (I.Null, A.raiseType (Dk', I.EClo (A.raiseType (G', U'), sk'))) ^ "\n")) else ()); New ) ) else lookup ((G, D, U, s), T, (((k, G', D', U'), {solutions = A; lookup = i}) :: T')) in  lookup ((G, D, U, s), (! table), []) )
(* ---------------------------------------------------------------------- *)

(* TOP LEVEL *)

let rec reset ()  = (table := [])
let rec solutions {solutions = S; lookup = i}  = S
let rec lookup {solutions = S; lookup = i}  = i
let rec noAnswers = function [] -> true | ((H) :: L') -> match (List.take (solutions (answ), lookup (answ))) with [] -> noAnswers L' | L -> false
let rec callCheck (G, D, U)  = match (! strategy) with Variant -> callCheckVariant (G, D, U) | Subsumption -> callCheckSubsumes (G, D, U)
let rec answCheck (G, D, U, s, O)  = match (! strategy) with Variant -> answCheckVariant (G, D, U, s, O) | Subsumption -> answCheckSubsumes (G, D, U, s, O)
(* needs to take into account previous size of table *)

let rec updateTable ()  = ( let rec update = function ([], T, Flag) -> (Flag, T) | ((((k, G, D, U), {solutions = S; lookup = i}) :: T), T', Flag) -> ( let l = length (S) in  if (l = i) then (* no new solutions were added in the previous stage *)
update T (((k, G, D, U), {solutions = S; lookup = List.length (S)}) :: T') Flag else (* new solutions were added *)
update T (((k, G, D, U), {solutions = S; lookup = List.length (S)}) :: T') true ) in let (Flag, T) = update (! table) [] false in let r = Flag || (! added) in  added := false; table := rev (T); (* in each stage incrementally increase termDepth *)
(*          termDepth := (!termDepth +1); *)
r )
(*  val termDepth = termDepth
    val ctxDepth = ctxDepth
    val ctxLength = ctxLength
*)

let table = table
let solutions = solutions
let lookup = lookup
let noAnswers = noAnswers
let reset = reset
let printTable = printTable
let printTableEntries = printTableEntries
let callCheck = callCheck
let answerCheck = answCheck
let updateTable = updateTable
(* local *)

 end


(* functor TableIndex *)

