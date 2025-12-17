TableIndex  Global GLOBAL    Queue QUEUE    Subordinate SUBORDINATE    Conv CONV    Unify UNIFY    AbstractTabled ABSTRACTTABLED    Whnf WHNF    Print PRINT    CPrint CPRINT    Names NAMES    TypeCheck TYPECHECK     TABLEINDEX  struct (*! structure IntSyn = IntSyn' !*)
(*! structure CompSyn = CompSyn' !*)
module (* TABLE

   table entry : D, G  |- u

   Answer substitution:

                 Dk, G  |- sk : D, G

   Answer :
                 Dk, G |- u[sk]
   *)
(* solution: (Dk, sk)

   * lookup  : pointer to the i-th element in solution list
   *)
type Answer(* entry = (((i, G, D, U), A)) where i is the access counter
   *)
type Entrytype Entriestype Indextype AnswStatetype Strategylet  in(* ---------------------------------------------------------------------- *)
(* global search parameters *)
let  in(* Subsumption *)
(* Variant *)
(* term abstraction after term depth is greater than 5 *)
let  inlet  inlet  in(*   val termDepth = ref (!globalTermDepth); *)
(*   val ctxDepth = ref (!globalCtxDepth);   *)
(*   val ctxLength = ref (!globalCtxLength); *)
(* apply strengthening during abstraction *)
let  in(* original query *)
let  in(* ---------------------------------------------------------------------- *)
module module module (* Global Table *)
let  in(* concat(Gdp, G) = G''
     *
     * if Gdp = ym...y1
     *    G   = xn...x1
     * then
     *    Gdp, G = G''
     *    ym...y1, xn...x1
     *
     *)
let rec concat(null,  , g') g' concat(decl (g,  , d),  , g') decl (concat (g,  , g'),  , d)let rec reverse(null,  , g') g' reverse(decl (g,  , d),  , g') reverse (g,  , decl (g',  , d))(* ---------------------------------------------------------------------- *)
(* printTable () = () *)
let rec printTable() let let rec proofTerms(g,  , d,  , u,  , []) print "" proofTerms(g,  , d,  , u,  , (((d',  , s'),  , _) :: s)) ((* (print (Print.expToString (I.Null,  *)
(*              A.raiseType(Names.ctxName(concat(G,D')), I.EClo(U, s')))) *)
(try  with ); (* do not print pskeletons *)
print ", \n\t"; proofTerms (g,  , d,  , u,  , s))let rec printT[] () printT(((k,  , g,  , d,  , u),  , {solutions = s; lookup = i}) :: t) match s with [] -> (printT t; print (expToString (null,  , raiseType (concat (g,  , d),  , u)) ^ ", NONE\n")) (a :: answ) -> (printT t; print (expToString (null,  , raiseType (concat (g,  , d),  , u)) ^ ", [\n\t"); proofTerms (g,  , d,  , u,  , (rev s)); print (" ] -- lookup : " ^ toString i ^ "\n\n")) in print ("Table: \n")printT (! table)print ("End Table \n")print ("Number of table entries   : " ^ toString (length (! table)) ^ "\n")(* printTableEntries () = () *)
let rec printTableEntries() let let rec printT[] () printT(((k,  , g,  , d,  , u),  , {solutions = s; lookup = i}) :: t) (printT t; print (expToString (null,  , raiseType (concat (g,  , d),  , u)) ^ "\n Access Counter : " ^ (toString (! k)) ^ " \n")) in print ("TableEntries: \n")printT (! table)print ("End TableEntries \n")print ("Number of table entries   : " ^ toString (length (! table)) ^ "\n")(* ---------------------------------------------------------------------- *)
(* Term Abstraction *)
let rec lengthSpine(nil) 0 lengthSpine(sClo (s,  , s')) 1 + lengthSpine (s)let rec exceedsTermDepth(i) match (! termDepth) with nONE -> false sOME (n) -> (i > n)let rec exceedsCtxDepth(i) match (! ctxDepth) with nONE -> false sOME (n) -> (print ("\n exceedsCtxDepth " ^ toString i ^ " > " ^ toString n ^ " ? "); (i > n))let rec exceedsCtxLength(i) match (! ctxLength) with nONE -> false sOME (n) -> (i > n)let rec max(x,  , y) if x > y then x else ylet rec oroption(nONE,  , nONE,  , nONE) false oroption(sOME (k),  , _,  , _) true oroption(_,  , sOME (n),  , _) true oroption(_,  , _,  , sOME (n)) truelet rec abstractionSet() oroption (! termDepth,  , ! ctxDepth,  , ! ctxLength)(* countDepth U =
         ctr = (ctrTerm, ctrDecl, ctrLength)
         ctrTerm : max term depth
         ctrDecl : max type depth in decl
         ctrLength : length of decl

    *)
let rec exceeds(u) countDecl (0,  , 0,  , u) countDecl(ctrType,  , ctrLength,  , pi ((d,  , _),  , v)) let let  in(*         val _ = print ("\n ctrType' = " ^ Int.toString ctrType')  *)
 in if ctrType' > ctrType then countDecl (ctrType',  , ctrLength + 1,  , v) else countDecl (ctrType,  , ctrLength + 1,  , v) countDecl(ctrType,  , ctrLength,  , u) let let  in(*         val _ = print ("\n 1 ctrTerm = " ^ Int.toString ctrTerm)
           val _ = print ("\n 1 ctxLength = " ^ Int.toString ctrLength)
           val _ = print ("\n 1 ctxDepth = " ^ Int.toString ctrType)
*)
 in exceedsCtxDepth (ctrType) || exceedsCtxLength (ctrLength) || exceedsTermDepth (count (0,  , u)) countDec(ctr,  , dec (_,  , u)) count (ctr,  , u) countDec(ctr,  , bDec (_,  , s)) 0 count(ctr,  , (u as uni (l))) ctr count(ctr,  , pi ((d,  , _),  , v)) let let  inlet  in(*         val _ = print ("\n ctrTerm = " ^ Int.toString ctrTerm)
           val _ = print ("\n ctrType = " ^ Int.toString ctrType)
*)
 in max (ctrType,  , ctrTerm)(* to revise ?*)
 count(ctr,  , root (f,  , s)) let let  in(*         val _ = print ("\n spineDepth = " ^ Int.toString ctrDepth)
           val _ = print ("\n RootF = " ^ Int.toString(ctrDepth + ctr))
*)
 in (ctrDepth + 1 + ctr)(*         (ctrLength + ctr) *)
 count(ctr,  , redex (u,  , s)) let let  inlet  in(*         val _ = print ("\n SpindeDepth = " ^ Int.toString ctrDepth)
           val _ = print ("\n Redex = " ^ Int.toString(max(ctrDepth',ctrDepth) + ctr))*)
 in (max (ctrDepth',  , ctrDepth) + ctr) count(ctr,  , lam (d,  , u)) count (ctr + 1,  , u) count(ctr,  , (x as eVar _)) ctr count(ctr,  , eClo (e,  , s)) count (ctr,  , e) count(ctr,  , (f as fgnExp (cs,  , ops))) (ctr)(* count max depth of term in S + length of S *)
 countSpine(ctrDepth,  , nil) ctrDepth countSpine(ctr,  , sClo (s,  , s')) countSpine (ctr,  , s) countSpine(ctrDepth,  , app (u,  , s)) let let  in in countSpine (max (ctrDepth',  , ctrDepth),  , s)(* ---------------------------------------------------------------------- *)
(* reinstSub (G, D, s) = s'
    *
    * If D', G |- s : D, G
    * then  G |- s' : D, G
    *)
let rec reinstSub(g,  , null,  , s) s reinstSub(g,  , decl (d,  , dec (_,  , a)),  , s) let let  in in dot (exp (x),  , reinstSub (g,  , d,  , s))(* ---------------------------------------------------------------------- *)
(* variant (U,s) (U',s')) = bool   *)
let rec variant(us,  , us') conv (us,  , us')(* subsumes ((G, D, U), (G', D', U')) = bool
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
let rec subsumes((g,  , d,  , u),  , (g',  , d',  , u')) let let  inlet  inlet  in in trail (fun () -> unifiable (d,  , (upi',  , s'),  , (upi,  , id)))let rec equalSub(shift k,  , shift k') (k = k') equalSub(dot (f,  , s),  , dot (f',  , s')) equalFront (f,  , f') && equalSub (s,  , s') equalSub(dot (f,  , s),  , shift k) false equalSub(shift k,  , dot (f,  , s)) false equalFront(idx n,  , idx n') (n = n') equalFront(exp u,  , exp v) conv ((u,  , id),  , (v,  , id)) equalFront(undef,  , undef) truelet rec equalSub1(dot (ms,  , s),  , dot (ms',  , s')) equalSub (s,  , s')let rec equalCtx(null,  , null) true equalCtx(decl (dk,  , dec (_,  , a)),  , decl (d1,  , dec (_,  , a1))) conv ((a,  , id),  , (a1,  , id)) && equalCtx (dk,  , d1)(* ---------------------------------------------------------------------- *)
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
let rec callCheckVariant(g,  , d,  , u) let let  inlet rec lookup((g,  , d,  , u),  , []) (table := ((ref 1,  , g,  , d,  , u),  , {solutions =  [][]; lookup =  00}) :: (! table); (if (! chatter) >= 5 then (print ("\n \n Added "); print (expToString (null,  , upi) ^ "\n to Table \n")) else ()); added := true; (* if termdepth(U) > n then force the tabled engine to suspend
               * and treat it like it is already in the table, but no answ available *)
if abstractionSet () then ((* print ("\n term " ^ Print.expToString (I.Null, Upi) ^
                  " exceeds depth or length ? \n"); *)
if exceeds (raiseType (g,  , u)) then ((if (! chatter) >= 5 then print ("\n term " ^ expToString (null,  , upi) ^ " exceeds depth or length \n") else ()); sOME ([])) else nONE) else nONE) lookup((g,  , d,  , u),  , ((h as ((k,  , g',  , d',  , u'),  , answ)) :: t)) if variant ((upi,  , id),  , (raiseType (concat (g',  , d'),  , u'),  , id)) then (k := ! k + 1; (if (! chatter) >= 5 then print ("call " ^ expToString (null,  , upi) ^ " found in table \n ") else ()); sOME [((g',  , d',  , u'),  , answ)]) else lookup ((g,  , d,  , u),  , t) in lookup ((g,  , d,  , u),  , (! table))(* Subsumption:

       Assumes: Table is in order [tn, ...., t1]
       i.e. tn is added to the table later than t1
            this implies that tn is more general than ti (i < n)

       if we find a tn s.t M is an instance of it, then return tn
       and do not search further

    *)
let rec callCheckSubsumes(g,  , d,  , u) let let rec lookup((g,  , d,  , u),  , []) (table := ((ref 1,  , g,  , d,  , u),  , {solutions =  [][]; lookup =  00}) :: (! table); (if (! chatter) >= 5 then print ("Added " ^ expToString (null,  , raiseType (concat (g,  , d),  , u)) ^ " to Table \n") else ()); added := true; if exceeds (raiseType (g,  , u)) then ((if (! chatter) >= 4 then print ("\n term " ^ expToString (null,  , raiseType (concat (g,  , d),  , u)) ^ " exceeds depth or length \n") else ()); sOME ([])) else nONE) lookup((g,  , d,  , u),  , (((k,  , g',  , d',  , u'),  , answ) :: t)) if (subsumes ((g,  , d,  , u),  , (g',  , d',  , u'))) then ((if (! chatter) >= 5 then print ("call " ^ expToString (null,  , raiseType (concat (g,  , d),  , u)) ^ "found in table \n ") else ()); k := ! k + 1; sOME ([((g',  , d',  , u'),  , answ)])) else lookup ((g,  , d,  , u),  , t) in lookup ((g,  , d,  , u),  , (! table))(* ---------------------------------------------------------------------- *)
let rec member((dk,  , sk),  , []) false member((dk,  , sk),  , (((d1,  , s1),  , _) :: s)) if equalSub (sk,  , s1) && equalCtx (dk,  , d1) then true else member ((dk,  , sk),  , s)(* answer check and insert

      if     G |- U[s]
          D, G |- U
             G |- s : D, G

      answerCheck (G, D, (U,s)) = repeated
         if s already occurs in answer list for U
      answerCheck (G, D, (U,s)) = new
         if s did not occur in answer list for U
         Sideeffect: update answer list for U

        Dk, G |- sk : D, G
        Dk, G |- U[sk]

        sk is the abstraction of s and Dk contains all "free" vars

     *)
let rec answCheckVariant(g,  , d,  , u,  , s,  , o) let let  inlet  inlet rec lookup(g,  , d,  , u,  , s)[]t (print (expToString (null,  , eClo (raiseType (g,  , u),  , s)) ^ " call should always be already in the table !\n"); repeated) lookup(g,  , d,  , u,  , s)((h as ((k,  , g',  , d',  , u'),  , {solutions = s; lookup = i})) :: t)t' if variant ((upi,  , id),  , (raiseType (concat (g',  , d'),  , u'),  , id)) then let let  in in (* answer check *)
if member ((dk,  , sk),  , s) then repeated else (table := (rev t') @ (((k,  , g',  , d',  , u'),  , {solutions =  (((dk,  , sk),  , o) :: s)(((dk,  , sk),  , o) :: s); lookup =  ii}) :: t); (if (! chatter) >= 5 then (print ("\n Add solution  -- "); print (expToString (null,  , eClo (raiseType (g',  , u'),  , s))); print ("\n solution added  -- "); print (expToString (null,  , raiseType (ctxName (dk),  , eClo (raiseType (g',  , u'),  , sk))))) else ()); new) else lookup (g,  , d,  , u,  , s) t (h :: t') in lookup (g,  , d,  , u,  , s) (! table) [](* memberSubsumes ((G, Dk, U, sk), (G', U', A)) = bool

   If Dk, G |- U[sk]

      A = ((Dn, sn), On), ....., ((D1, s1), O1)

      for all i in [1, ..., n]
          Di, G' |- U'[si]
              G' |- si' : Di, G'
   then
     exists an i in [1,...,n]  s.t.
         Dk, G |- U[sk] is an instance of G' |- U'[si']
   *)
let rec memberSubsumes((g,  , d,  , u,  , s),  , (g',  , u',  , [])) false memberSubsumes((g,  , d,  , u,  , s),  , (g',  , u',  , (((d1,  , s1),  , _) :: a))) let let  inlet  inlet  inlet  in(* assume G' and G are the same for now *)
let  in in if b then ((if (! chatter) >= 5 then print "\n answer in table subsumes answer \n " else ()); true) else memberSubsumes ((g,  , d,  , u,  , s),  , (g',  , u',  , a))let rec shift(0,  , s) s shift(n,  , s) shift (n - 1,  , dot1 s)let rec answCheckSubsumes(g,  , d,  , u,  , s,  , o) let let  inlet  inlet rec lookup((g,  , d,  , u,  , s),  , [],  , t) (print (expToString (concat (g,  , d),  , eClo (u,  , s)) ^ " call should always be already in the table !\n"); repeated) lookup((g,  , d,  , u,  , s),  , (((k,  , g',  , d',  , u'),  , {solutions = a; lookup = i}) :: t),  , t') if (subsumes ((g,  , d,  , u),  , (g',  , d',  , u'))) then let let  in in if memberSubsumes ((g,  , dk,  , u,  , sk),  , (g',  , u',  , a)) then repeated else let let  inlet  in(*  higher-order matching *)
let  inlet  inlet  in(* reinstantiate us' *)
 in (match ! query with nONE -> ()(* nothing to do *)
 sOME (g1,  , d1,  , u1,  , s1,  , sc1) -> ((if (! chatter) >= 4 then (print ("Generate answers for: "); print (expToString (null,  , eClo (raiseType (g1,  , u1),  , s1)) ^ " \n"); print ("Answer in table: "); print (expToString (null,  , raiseType (dk,  , eClo (raiseType (g',  , u'),  , s'))) ^ " : \n"); print (expToString (null,  , eClo (raiseType (dk,  , eClo (raiseType (g',  , u'),  , sk')),  , rs)) ^ " : \n")) else ()); (if (subsumes ((g1,  , d1,  , u1),  , (g',  , d',  , u'))) then (* original query is an instance of the entry we are adding answ to *)
trail (fun () -> (if unifiable (d1,  , (raiseType (g1,  , u1),  , s1),  , (eClo (raiseType (g',  , u'),  , sk'),  , rs)) then let let  in in (* (I.EClo(N1, I.comp(shift(I.ctxLength(Gdp1),s1), w))) *)
sc1 o else ())) else ())))table := ((rev t') @ (((k,  , g',  , d',  , u'),  , {solutions =  (((dk',  , sk'),  , o) :: a)(((dk',  , sk'),  , o) :: a); lookup =  ii}) :: t))(if (! chatter) >= 5 then (print ("\n \n solution (original) was: \n"); print (expToString (null,  , eClo (raiseType (g,  , u),  , s)) ^ "\n"); print ("\n \n solution (deref) was: \n"); print (expToString (null,  , raiseType (dk,  , eClo (raiseType (g,  , u),  , sk))) (*                    print(Print.expToString(I.Null, I.EClo(A.raiseType(concat(G, Dk), U), sk)) *)
 ^ "\n"); print ("\n solution added  --- "); print (expToString (null,  , raiseType (dk',  , eClo (raiseType (g',  , u'),  , s'))) ^ "\n"); print ("\n solution added (dereferenced) --- "); print (expToString (null,  , raiseType (dk',  , eClo (raiseType (g',  , u'),  , sk'))) ^ "\n")) else ())new else lookup ((g,  , d,  , u,  , s),  , t,  , (((k,  , g',  , d',  , u'),  , {solutions =  aa; lookup =  ii}) :: t')) in lookup ((g,  , d,  , u,  , s),  , (! table),  , [])(* ---------------------------------------------------------------------- *)
(* TOP LEVEL *)
let rec reset() (table := [])let rec solutions{solutions = s; lookup = i} slet rec lookup{solutions = s; lookup = i} ilet rec noAnswers[] true noAnswers((h as ((g',  , d',  , u'),  , answ)) :: l') match (take (solutions (answ),  , lookup (answ))) with [] -> noAnswers l' l -> falselet rec callCheck(g,  , d,  , u) match (! strategy) with variant -> callCheckVariant (g,  , d,  , u) subsumption -> callCheckSubsumes (g,  , d,  , u)let rec answCheck(g,  , d,  , u,  , s,  , o) match (! strategy) with variant -> answCheckVariant (g,  , d,  , u,  , s,  , o) subsumption -> answCheckSubsumes (g,  , d,  , u,  , s,  , o)(* needs to take into account previous size of table *)
let rec updateTable() let let rec update[]tflag (flag,  , t) update(((k,  , g,  , d,  , u),  , {solutions = s; lookup = i}) :: t)t'flag let let  in in if (l = i) then (* no new solutions were added in the previous stage *)
update t (((k,  , g,  , d,  , u),  , {solutions =  ss; lookup =  length (s)length (s)}) :: t') flag else (* new solutions were added *)
update t (((k,  , g,  , d,  , u),  , {solutions =  ss; lookup =  length (s)length (s)}) :: t') truelet  inlet  in in added := falsetable := rev (t)(* in each stage incrementally increase termDepth *)
(*          termDepth := (!termDepth +1); *)
r(*  val termDepth = termDepth
    val ctxDepth = ctxDepth
    val ctxLength = ctxLength
*)
let  inlet  inlet  inlet  inlet  inlet  inlet  inlet  inlet  inlet  in(* local *)
end