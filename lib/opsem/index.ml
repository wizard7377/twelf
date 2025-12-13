(* Indexing for table *)
(* Author: Brigitte Pientka *)

functor (* GEN BEGIN FUNCTOR DECL *) TableIndex (structure Global : GLOBAL
                    structure Queue : QUEUE
                    (*! structure IntSyn' : INTSYN !*)
                    (*! structure CompSyn': COMPSYN !*)
                    (*! sharing CompSyn'.IntSyn = IntSyn' !*)
                    structure Subordinate : SUBORDINATE
                    (*! sharing Subordinate.IntSyn = IntSyn'                   !*)
                    structure Conv: CONV
                    (*! sharing Conv.IntSyn = IntSyn' !*)
                    structure Unify : UNIFY
                    (*! sharing Unify.IntSyn = IntSyn' !*)
                    structure AbstractTabled : ABSTRACTTABLED
                    (*! sharing AbstractTabled.IntSyn = IntSyn' !*)
                    structure Whnf : WHNF
                    (*! sharing Whnf.IntSyn = IntSyn' !*)
                    structure Print : PRINT
                    (*! sharing Print.IntSyn = IntSyn' !*)
                    structure CPrint : CPRINT
                    (*! sharing CPrint.IntSyn = IntSyn' !*)
                    (*! sharing CPrint.CompSyn = CompSyn' !*)
                    structure Names : NAMES
                    (*! sharing Names.IntSyn = IntSyn' !*)
                    structure TypeCheck : TYPECHECK
                    (*! sharing TypeCheck.IntSyn = IntSyn' !*)
                 )
  : TABLEINDEX =
struct
  (*! structure IntSyn = IntSyn' !*)
  (*! structure CompSyn = CompSyn' !*)
  structure Conv = Conv


  (* TABLE

   table entry : D, G  |- u

   Answer substitution:

                 Dk, G  |- sk : D, G

   Answer :
                 Dk, G |- u[sk]
   *)

  (* solution: (Dk, sk)

   * lookup  : pointer to the i-th element in solution list
   *)

  type answer = {solutions : ((IntSyn.dctx * IntSyn.sub) * CompSyn.pskeleton) list,
                 lookup: int}

  (* entry = (((i, G, D, U), A)) where i is the access counter
   *)
  type entry = (((int ref * IntSyn.dctx * IntSyn.dctx * IntSyn.exp) * answer))

  type entries = entry list

  type index = entry list

  datatype answ_state = New | Repeated

  datatype strategy = Variant | Subsumption

  (* GEN BEGIN TAG OUTSIDE LET *) val added = ref false (* GEN END TAG OUTSIDE LET *);

  (* ---------------------------------------------------------------------- *)
  (* global search parameters *)

  (* GEN BEGIN TAG OUTSIDE LET *) val strategy  = ref Variant (* GEN END TAG OUTSIDE LET *) (* Subsumption *) (* Variant *)

  (* term abstraction after term depth is greater than 5 *)
  (* GEN BEGIN TAG OUTSIDE LET *) val termDepth = ref NONE : int option ref (* GEN END TAG OUTSIDE LET *);
  (* GEN BEGIN TAG OUTSIDE LET *) val ctxDepth = ref NONE : int option ref (* GEN END TAG OUTSIDE LET *);
  (* GEN BEGIN TAG OUTSIDE LET *) val ctxLength = ref NONE : int option ref (* GEN END TAG OUTSIDE LET *);

(*   val termDepth = ref (!globalTermDepth); *)
(*   val ctxDepth = ref (!globalCtxDepth);   *)
(*   val ctxLength = ref (!globalCtxLength); *)

  (* apply strengthening during abstraction *)
  (* GEN BEGIN TAG OUTSIDE LET *) val strengthen = AbstractTabled.strengthen (* GEN END TAG OUTSIDE LET *) ;

  (* original query *)
  (* GEN BEGIN TAG OUTSIDE LET *) val query : (IntSyn.dctx * IntSyn.dctx  * IntSyn.exp * IntSyn.sub * (CompSyn.pskeleton -> unit))
                option ref = ref NONE (* GEN END TAG OUTSIDE LET *)

  (* ---------------------------------------------------------------------- *)

  local
    structure I = IntSyn
    structure C = CompSyn
    structure A = AbstractTabled

    (* Global Table *)

    (* GEN BEGIN TAG OUTSIDE LET *) val table : index ref = ref [] (* GEN END TAG OUTSIDE LET *)

    (* concat(Gdp, G) = G''
     *
     * if Gdp = ym...y1
     *    G   = xn...x1
     * then
     *    Gdp, G = G''
     *    ym...y1, xn...x1
     *
     *)
    fun (* GEN BEGIN FUN FIRST *) concat (I.Null, G') = G' (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) concat (I.Decl(G, D), G') = I.Decl(concat(G,G'), D) (* GEN END FUN BRANCH *)



   fun (* GEN BEGIN FUN FIRST *) reverse (I.Null, G') = G' (* GEN END FUN FIRST *)
     | (* GEN BEGIN FUN BRANCH *) reverse (I.Decl(G, D), G') =
         reverse (G, I.Decl(G', D)) (* GEN END FUN BRANCH *)

    (* ---------------------------------------------------------------------- *)

    (* printTable () = () *)

    fun printTable () =
      let
        fun (* GEN BEGIN FUN FIRST *) proofTerms (G, D, U, []) = print "" (* GEN END FUN FIRST *)
          | (* GEN BEGIN FUN BRANCH *) proofTerms (G, D, U, (((D', s'), _)::S)) =
          ((* (print (Print.expToString (I.Null,  *)
              (*              A.raiseType(Names.ctxName(concat(G,D')), I.EClo(U, s')))) *)
              
           (print (Print.expToString (I.Null, A.raiseType(Names.ctxName(D'),
                        I.EClo(A.raiseType(Names.ctxName(G), U), s'))))
            handle _ => print "EXCEPTION" );
           (* do not print pskeletons *)
           print ", \n\t";
           proofTerms (G, D, U, S)) (* GEN END FUN BRANCH *)
    
        fun (* GEN BEGIN FUN FIRST *) printT [] = () (* GEN END FUN FIRST *)
          | (* GEN BEGIN FUN BRANCH *) printT (((k, G, D, U), {solutions =  S, lookup = i})::T) =
            case S
              of [] => (printT T ;
                        print (Print.expToString (I.Null,
                                                  A.raiseType(concat(G, D), U))
                               ^ ", NONE\n"))
              | (a::answ) => (printT T;
                              print (Print.expToString (I.Null,
                                                        A.raiseType(concat(G, D), U)) ^
                                     ", [\n\t");
                              proofTerms (G, D, U, (rev S));
                              print (" ] -- lookup : " ^ Int.toString i ^ "\n\n")) (* GEN END FUN BRANCH *)
      in
        print ("Table: \n");
        printT (!table);
        print ("End Table \n");
        print ("Number of table entries   : " ^ Int.toString(length(!table)) ^ "\n")
      end


    (* printTableEntries () = () *)

    fun printTableEntries () =
      let
        fun (* GEN BEGIN FUN FIRST *) printT [] = () (* GEN END FUN FIRST *)
          | (* GEN BEGIN FUN BRANCH *) printT (((k, G, D, U), {solutions =  S, lookup = i})::T) =
          (printT T ;
           print (Print.expToString (I.Null,
                                     A.raiseType(concat(G, D), U)) ^ "\n Access Counter : " ^ (Int.toString (!k)) ^ " \n")) (* GEN END FUN BRANCH *)
      in
        print ("TableEntries: \n");
        printT (!table);
        print ("End TableEntries \n");
        print ("Number of table entries   : " ^ Int.toString(length(!table)) ^ "\n")
      end


    (* ---------------------------------------------------------------------- *)

    (* Term Abstraction *)

    fun (* GEN BEGIN FUN FIRST *) lengthSpine (I.Nil) = 0 (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) lengthSpine (I.SClo(S, s')) = 1 + lengthSpine(S) (* GEN END FUN BRANCH *)


    fun exceedsTermDepth (i) =
      case (!termDepth) of
        NONE => false
      | SOME(n) => (i > n)

    fun exceedsCtxDepth (i) =
      case (!ctxDepth) of
        NONE => false
      | SOME(n) => (print ("\n exceedsCtxDepth " ^Int.toString i ^ " > " ^ Int.toString n ^ " ? ") ;(i > n))

    fun exceedsCtxLength (i) =
      case (!ctxLength) of
        NONE => false
      | SOME(n) => (i > n)

    fun max (x,y) =
      if x > y then x
      else y

    fun (* GEN BEGIN FUN FIRST *) oroption (NONE, NONE, NONE) = false (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) oroption (SOME(k), _ , _) = true (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) oroption (_ , SOME(n), _) = true (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) oroption (_ , _, SOME(n)) = true (* GEN END FUN BRANCH *)

    fun abstractionSet () =
      oroption(!termDepth, !ctxDepth, !ctxLength)

    (* countDepth U =
         ctr = (ctrTerm, ctrDecl, ctrLength)
         ctrTerm : max term depth
         ctrDecl : max type depth in decl
         ctrLength : length of decl

    *)

    fun exceeds (U) = countDecl(0,0, U)

    and (* GEN BEGIN FUN FIRST *) countDecl (ctrType, ctrLength, I.Pi((D, _), V)) =
         let
           (* GEN BEGIN TAG OUTSIDE LET *) val ctrType' = countDec(0, D) (* GEN END TAG OUTSIDE LET *)
    (*         val _ = print ("\n ctrType' = " ^ Int.toString ctrType')  *)
         in
           if ctrType' > ctrType then
             countDecl (ctrType', ctrLength + 1, V)
           else
             countDecl (ctrType, ctrLength + 1, V)
         end (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) countDecl(ctrType, ctrLength, U) =
         let
           (* GEN BEGIN TAG OUTSIDE LET *) val ctrTerm = count (0, U) (* GEN END TAG OUTSIDE LET *)
      (*         val _ = print ("\n 1 ctrTerm = " ^ Int.toString ctrTerm)
           val _ = print ("\n 1 ctxLength = " ^ Int.toString ctrLength)
           val _ = print ("\n 1 ctxDepth = " ^ Int.toString ctrType)
      *)
         in
           exceedsCtxDepth(ctrType) orelse
           exceedsCtxLength(ctrLength) orelse
           exceedsTermDepth(count(0,U))
         end (* GEN END FUN BRANCH *)

    and (* GEN BEGIN FUN FIRST *) countDec (ctr, I.Dec(_, U)) = count(ctr, U) (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) countDec (ctr, I.BDec(_,s)) = 0 (* GEN END FUN BRANCH *)

    and (* GEN BEGIN FUN FIRST *) count (ctr, (U as I.Uni (L))) = ctr (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) count (ctr, I.Pi((D, _), V)) =
          let
            (* GEN BEGIN TAG OUTSIDE LET *) val ctrTerm = count (ctr, V) (* GEN END TAG OUTSIDE LET *)
            (* GEN BEGIN TAG OUTSIDE LET *) val ctrType = countDec (ctr, D) (* GEN END TAG OUTSIDE LET *)
      (*         val _ = print ("\n ctrTerm = " ^ Int.toString ctrTerm)
           val _ = print ("\n ctrType = " ^ Int.toString ctrType)
      *)
      
          in
          max(ctrType,ctrTerm) (* to revise ?*)
          end (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) count (ctr, I.Root (F, S)) =
         let
           (* GEN BEGIN TAG OUTSIDE LET *) val ctrDepth = countSpine (1, S) (* GEN END TAG OUTSIDE LET *)
      (*         val _ = print ("\n spineDepth = " ^ Int.toString ctrDepth)
           val _ = print ("\n RootF = " ^ Int.toString(ctrDepth + ctr))
      *)
         in
           (ctrDepth + 1 + ctr)
      (*         (ctrLength + ctr) *)
         end (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) count (ctr, I.Redex (U, S)) =
         let
           (* GEN BEGIN TAG OUTSIDE LET *) val ctrDepth = count (0, U) (* GEN END TAG OUTSIDE LET *)
           (* GEN BEGIN TAG OUTSIDE LET *) val ctrDepth' =  countSpine (ctrDepth, S) (* GEN END TAG OUTSIDE LET *)
      (*         val _ = print ("\n SpindeDepth = " ^ Int.toString ctrDepth)
           val _ = print ("\n Redex = " ^ Int.toString(max(ctrDepth',ctrDepth) + ctr))*)
      
         in
           (max(ctrDepth',ctrDepth) + ctr)
         end (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) count (ctr, I.Lam (D, U)) =
         count (ctr+1, U) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) count (ctr, (X as I.EVar _)) =
         (* shouldn't happen *)
         ctr (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) count (ctr, I.EClo(E, s)) =
         count (ctr, E) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) count (ctr, (F as I.FgnExp (cs, ops))) =
         (* shouldn't happen *)
         (ctr) (* GEN END FUN BRANCH *)

 (* count max depth of term in S + length of S *)
    and (* GEN BEGIN FUN FIRST *) countSpine (ctrDepth, I.Nil)  = ctrDepth (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) countSpine (ctr, I.SClo (S, s')) =
         (* ? *)
         countSpine (ctr, S) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) countSpine (ctrDepth, I.App (U, S)) =
         let
           (* GEN BEGIN TAG OUTSIDE LET *) val ctrDepth' = count (0, U) (* GEN END TAG OUTSIDE LET *)
         in
           countSpine (max(ctrDepth', ctrDepth), S)
      end (* GEN END FUN BRANCH *)



   (* ---------------------------------------------------------------------- *)
   (* reinstSub (G, D, s) = s'
    *
    * If D', G |- s : D, G
    * then  G |- s' : D, G
    *)

   fun (* GEN BEGIN FUN FIRST *) reinstSub (G, I.Null, s) = s (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) reinstSub (G, I.Decl(D, I.Dec(_,A)), s) =
      let
        (* GEN BEGIN TAG OUTSIDE LET *) val X = I.newEVar (I.Null, A) (* GEN END TAG OUTSIDE LET *)
      in
        I.Dot(I.Exp(X), reinstSub (G, D, s))
      
      end (* GEN END FUN BRANCH *)


   (* ---------------------------------------------------------------------- *)
   (* variant (U,s) (U',s')) = bool   *)

    fun variant (Us, Us') = Conv.conv (Us, Us')

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
    fun subsumes ((G, D, U), (G', D', U')) =
      let
        (* GEN BEGIN TAG OUTSIDE LET *) val Upi = A.raiseType (G, U) (* GEN END TAG OUTSIDE LET *)
        (* GEN BEGIN TAG OUTSIDE LET *) val Upi' = A.raiseType (G', U') (* GEN END TAG OUTSIDE LET *)
        (* GEN BEGIN TAG OUTSIDE LET *) val s' = reinstSub (G', D', I.id) (* GEN END TAG OUTSIDE LET *)
      in
        CSManager.trail ((* GEN BEGIN FUNCTION EXPRESSION *) fn () =>
                         Unify.unifiable (D, (Upi', s'), (Upi, I.id)) (* GEN END FUNCTION EXPRESSION *))
      end


    fun (* GEN BEGIN FUN FIRST *) equalSub (I.Shift k, I.Shift k') = (k = k') (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) equalSub (I.Dot(F, S), I.Dot(F', S')) =
        equalFront (F, F') andalso equalSub (S, S') (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) equalSub (I.Dot(F,S), I.Shift k) = false (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) equalSub (I.Shift k, I.Dot(F,S)) = false (* GEN END FUN BRANCH *)

    and (* GEN BEGIN FUN FIRST *) equalFront (I.Idx n, I.Idx n') = (n = n') (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) equalFront (I.Exp U, I.Exp V) = Conv.conv ((U, I.id), (V, I.id)) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) equalFront (I.Undef, I.Undef) = true (* GEN END FUN BRANCH *)

    fun equalSub1 (I.Dot(ms, s), I.Dot(ms', s')) =
          equalSub (s, s')


    fun (* GEN BEGIN FUN FIRST *) equalCtx (I.Null, I.Null) = true (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) equalCtx (I.Decl(Dk, I.Dec(_, A)), I.Decl(D1, I.Dec(_, A1))) =
        Conv.conv ((A, I.id), (A1, I.id)) andalso equalCtx(Dk, D1) (* GEN END FUN BRANCH *)

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

    fun callCheckVariant (G, D, U) =
      let
        (* GEN BEGIN TAG OUTSIDE LET *) val Upi = A.raiseType(concat(G, D), U) (* GEN END TAG OUTSIDE LET *)
        fun (* GEN BEGIN FUN FIRST *) lookup ((G, D, U), []) =
          (table := ((ref 1, G, D, U), {solutions = [],lookup = 0})::(!table);
           (if (!Global.chatter) >= 5 then
              (print ("\n \n Added " );
               print (Print.expToString (I.Null, Upi) ^ "\n to Table \n"))
            else
              ());
              added := true;
              (* if termdepth(U) > n then force the tabled engine to suspend
               * and treat it like it is already in the table, but no answ available *)
              if abstractionSet() then
                ((* print ("\n term " ^ Print.expToString (I.Null, Upi) ^
                  " exceeds depth or length ? \n"); *)
            
                 if exceeds (A.raiseType(G, U)) then
                   ((if (!Global.chatter) >= 5 then
                       print ("\n term " ^ Print.expToString (I.Null, Upi) ^
                              " exceeds depth or length \n")
                     else
                       ());
                       SOME([]))
                 else
                   NONE)
              else
                NONE) (* GEN END FUN FIRST *)
          | (* GEN BEGIN FUN BRANCH *) lookup ((G, D, U), ((H as ((k, G', D', U'), answ))::T)) =
            if variant ((Upi, I.id), (A.raiseType(concat(G',D'), U'), I.id)) then
              (k := !k+1;
               (if (!Global.chatter) >= 5 then
                  print ("call " ^ Print.expToString (I.Null, Upi) ^ " found in table \n ")
                else
                  ());
                  SOME[((G', D', U'), answ)])
            else
              lookup ((G, D, U), T) (* GEN END FUN BRANCH *)
      in
        lookup ((G, D, U), (!table))
      end


    (* Subsumption:

       Assumes: Table is in order [tn, ...., t1]
       i.e. tn is added to the table later than t1
            this implies that tn is more general than ti (i < n)

       if we find a tn s.t M is an instance of it, then return tn
       and do not search further

    *)


    fun callCheckSubsumes (G, D, U) =
      let
        fun (* GEN BEGIN FUN FIRST *) lookup ((G, D, U), []) =
            (table := ((ref 1, G, D, U), {solutions = [],lookup = 0})::(!table);
             (if (!Global.chatter) >= 5 then
                print ("Added " ^  Print.expToString (I.Null,A.raiseType(concat(G, D), U)) ^ " to Table \n")
              else
                ());
             added := true;
             if exceeds (A.raiseType(G, U)) then
                ((if (!Global.chatter) >= 4 then
                    print ("\n term " ^ Print.expToString (I.Null, A.raiseType(concat(G, D), U)) ^
                           " exceeds depth or length \n")
                  else
                    ());
                SOME([]))
              else
                NONE) (* GEN END FUN FIRST *)
          | (* GEN BEGIN FUN BRANCH *) lookup ((G, D, U), (((k, G', D', U'), answ)::T)) =
            if (subsumes ((G, D, U), (G', D', U'))) then
              ((if (!Global.chatter) >= 5 then
                 print ("call " ^ Print.expToString (I.Null, A.raiseType(concat(G, D), U)) ^ "found in table \n ")
               else
                 ());
                  k := !k+1;
                 SOME([((G', D', U'), answ)]))
            else
              lookup ((G, D, U), T) (* GEN END FUN BRANCH *)
      in
        lookup ((G, D, U), (!table))
      end

    (* ---------------------------------------------------------------------- *)
    fun (* GEN BEGIN FUN FIRST *) member ((Dk, sk), []) = false (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) member ((Dk, sk), (((D1, s1),_)::S)) =
      (* do we really need to compare Gus and Gs1 ?  *)
      if equalSub (sk,s1) andalso equalCtx (Dk, D1) then
        true
      else
        member ((Dk, sk), S) (* GEN END FUN BRANCH *)

    (* answer check and insert

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
    fun answCheckVariant (G, D, U, s, O) =
      let
        (* GEN BEGIN TAG OUTSIDE LET *) val Upi = A.raiseType(concat(G, D), U) (* GEN END TAG OUTSIDE LET *)
    
        (* GEN BEGIN TAG OUTSIDE LET *) val _ = if (!Global.chatter) >= 5 then
                  (print "\n AnswCheckInsert: ";
                   print (Print.expToString(I.Null,
                                            I.EClo(A.raiseType(G, U),s)) ^ "\n");
                   print "\n Table Index : " ;
                   print (Print.expToString (I.Null,  Upi) ^ "\n"))
                else
                  () (* GEN END TAG OUTSIDE LET *)
    
        fun (* GEN BEGIN FUN FIRST *) lookup  (G, D, U, s) [] T =
          (* cannot happen ! *)
          (print (Print.expToString(I.Null, I.EClo(A.raiseType(G,U),s))
                  ^ " call should always be already in the table !\n") ;
           Repeated) (* GEN END FUN FIRST *)
          | (* GEN BEGIN FUN BRANCH *) lookup (G, D, U, s) ((H as ((k, G', D',U'),
                    {solutions = S, lookup = i}))::T) T' =
          if variant ((Upi, I.id),
                      (A.raiseType(concat(G', D'), U'), I.id))
            then
              let
                (* GEN BEGIN TAG OUTSIDE LET *) val (Dk, sk) = A.abstractAnswSub s (* GEN END TAG OUTSIDE LET *)
              in
                (* answer check *)
                if member ((Dk, sk), S) then
                  Repeated
                else
                  (table := (rev T')@(((k, G', D', U'),
                                       {solutions = (((Dk, sk), O)::S),
                                        lookup = i})::T);
              
                   (if (!Global.chatter) >= 5 then
                      (print ("\n Add solution  -- " );
                       print (Print.expToString(I.Null,
                                I.EClo(A.raiseType(G', U'), s)));
                       print ("\n solution added  -- " );
                       print (Print.expToString(I.Null,
                        A.raiseType(Names.ctxName(Dk),
                                    I.EClo(A.raiseType(G', U'), sk)))))
                    else
                      ());
                   New)
              end
           else
              lookup (G, D, U, s) T (H::T') (* GEN END FUN BRANCH *)
      in
        lookup (G, D, U, s) (!table) []
      end

  (* memberSubsumes ((G, Dk, U, sk), (G', U', A)) = bool

   If Dk, G |- U[sk]

      A = ((Dn, sn), On), ....., ((D1, s1), O1)

      for all i in [1, ..., n]
          Di, G' |- U'[si]
              G' |- si' : Di, G'
   then
     exists an i in [1,...,n]  s.t.
         Dk, G |- U[sk] is an instance of G' |- U'[si']
   *)

    fun (* GEN BEGIN FUN FIRST *) memberSubsumes ((G, D, U, s), (G', U', [])) = false (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) memberSubsumes ((G, D, U, s), (G', U', (((D1, s1), _)::A))) =
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val Upi = A.raiseType(G, U) (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val Upi' = A.raiseType(G',U') (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val s1' = reinstSub (G', D1, I.id) (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val Vpis = (I.EClo(Upi', s1), s1') (* GEN END TAG OUTSIDE LET *)
      
          (* assume G' and G are the same for now *)
          (* GEN BEGIN TAG OUTSIDE LET *) val b = CSManager.trail ((* GEN BEGIN FUNCTION EXPRESSION *) fn () =>
                                   Unify.unifiable (D, (Upi, s), (Vpis)) (* GEN END FUNCTION EXPRESSION *)) (* GEN END TAG OUTSIDE LET *)
        in
          if b then
            ((if (!Global.chatter) >= 5 then
                print "\n answer in table subsumes answer \n "
              else
                ());
             true)
          else
            memberSubsumes ((G, D, U, s), (G', U', A))
        end (* GEN END FUN BRANCH *)

  fun (* GEN BEGIN FUN FIRST *) shift (0, s) = s (* GEN END FUN FIRST *)
    | (* GEN BEGIN FUN BRANCH *) shift (n, s) = shift(n-1, I.dot1 s) (* GEN END FUN BRANCH *)


   fun answCheckSubsumes (G, D, U, s, O) =
      let
        (* GEN BEGIN TAG OUTSIDE LET *) val Upi = A.raiseType(G, U) (* GEN END TAG OUTSIDE LET *)
        (* GEN BEGIN TAG OUTSIDE LET *) val _ = if (!Global.chatter) >= 4 then
                    (print ("\n AnswCheckInsert (subsumes): " );
                     print(Print.expToString(I.Null, I.EClo(Upi, s))
                       ^ "\n"))
                else () (* GEN END TAG OUTSIDE LET *)
   
        fun (* GEN BEGIN FUN FIRST *) lookup ((G, D, U , s), [], T) =
          (* cannot happen ! *)
          (print (Print.expToString(concat(G, D), I.EClo(U,s))
                  ^ " call should always be already in the table !\n") ;
           Repeated) (* GEN END FUN FIRST *)
          | (* GEN BEGIN FUN BRANCH *) lookup ((G, D, U, s), (((k, G', D', U'), {solutions = A, lookup = i})::T), T') =
          if (subsumes ((G, D, U), (G', D', U'))) then
            let
              (* GEN BEGIN TAG OUTSIDE LET *) val (Dk, sk) = A.abstractAnswSub s (* GEN END TAG OUTSIDE LET *)
             in
               if memberSubsumes ((G, Dk, U, sk), (G', U', A)) then
                 Repeated
               else
                 let
                   (* GEN BEGIN TAG OUTSIDE LET *) val s' = reinstSub (G', D', I.id) (* GEN END TAG OUTSIDE LET *)
                   (* GEN BEGIN TAG OUTSIDE LET *) val _ = if (!Global.chatter) >= 4 then
                            (print "\n new answer to be added to Index \n";
                             print (Print.expToString(I.Null,
                                                    A.raiseType(concat(G', D'), U')) ^"\n");
                             print "\n answer added \n";
                             print (Print.expToString(I.Null, A.raiseType(Dk,
                                        I.EClo(A.raiseType(G, U), sk))) ^ "\n"))
                           else
                             () (* GEN END TAG OUTSIDE LET *)
                   (*  higher-order matching *)
                   (* GEN BEGIN TAG OUTSIDE LET *) val _ = if (Unify.unifiable (Dk, (A.raiseType(G, U), sk),
                                               (A.raiseType(G', U'), s')))
                             then (if (!Global.chatter) >= 4 then
                                     (print "\n1 unification successful !\n";
                                      print (Print.expToString(I.Null, A.raiseType(Dk,
                                              I.EClo(A.raiseType(G', U'), s')))
                                             ^ "\n"))
                                   else
                                     ())
                           else print "\n1 unification failed! -- should never happen ?" (* GEN END TAG OUTSIDE LET *)
                   (* GEN BEGIN TAG OUTSIDE LET *) val (Dk', sk') = A.abstractAnsw (Dk, s') (* GEN END TAG OUTSIDE LET *)
                   (* GEN BEGIN TAG OUTSIDE LET *) val rs = reinstSub (G', Dk', I.id) (* GEN END TAG OUTSIDE LET *) (* reinstantiate us' *)
                in
                  (case !query of
                    NONE => () (* nothing to do *)
                    | SOME(G1, D1, U1, s1, sc1) =>
                      ((if (!Global.chatter) >= 4 then
                              (print ("Generate answers for: " );
                               print (Print.expToString(I.Null, I.EClo(A.raiseType(G1, U1), s1)) ^ " \n");
                               print ("Answer in table: " );
                               print (Print.expToString(I.Null, A.raiseType(Dk, I.EClo(A.raiseType(G', U'), s')))
                                      ^ " : \n" );
                               print (Print.expToString(I.Null, I.EClo(A.raiseType(Dk, I.EClo(A.raiseType(G', U'), sk')), rs)) ^ " : \n" ))
                           else ());
                       (if (subsumes ((G1, D1, U1), (G', D', U'))) then
                         (* original query is an instance of the entry we are adding answ to *)
                         CSManager.trail ((* GEN BEGIN FUNCTION EXPRESSION *) fn () =>
                             (if Unify.unifiable (D1, (A.raiseType(G1, U1), s1),
                                                  (I.EClo(A.raiseType(G', U'), sk'), rs))
                                then
                                  let
                                    (* GEN BEGIN TAG OUTSIDE LET *) val w = if (!strengthen)
                                              then
                                                Subordinate.weaken (I.Null, IntSyn.targetFam(I.EClo(U1, s1)))
                                            else
                                              I.id (* GEN END TAG OUTSIDE LET *)
                                  in
                                                 (* (I.EClo(N1, I.comp(shift(I.ctxLength(Gdp1),s1), w))) *)
                                                 sc1 O
                                               end
                                           else ()
                                             ) (* GEN END FUNCTION EXPRESSION *))
                       else
                         ())));
             
                  table := ((rev T')@(((k, G', D', U'),
                                       {solutions = (((Dk', sk'), O)::A),
                                        lookup = i})::T));
                  (if (!Global.chatter) >= 5 then
                     (print ("\n \n solution (original) was: \n");
                      print(Print.expToString(I.Null, I.EClo(A.raiseType(G, U), s))
                            ^ "\n");
                      print ("\n \n solution (deref) was: \n");
                      print(Print.expToString(I.Null, A.raiseType(Dk, I.EClo(A.raiseType(G, U), sk)))
             (*                    print(Print.expToString(I.Null, I.EClo(A.raiseType(concat(G, Dk), U), sk)) *)
                            ^ "\n");
                      print ("\n solution added  --- ");
                      print (Print.expToString(I.Null, A.raiseType(Dk', I.EClo(A.raiseType(G', U'), s')))
                             ^ "\n");
                      print ("\n solution added (dereferenced) --- ");
                      print (Print.expToString(I.Null, A.raiseType(Dk',
                                               I.EClo(A.raiseType(G', U'), sk')))
                             ^ "\n"))
                  else
                    ());
                  New
                end
             end
          else
            lookup ((G, D, U, s), T, (((k, G', D', U'), {solutions = A, lookup = i})::T')) (* GEN END FUN BRANCH *)
      in
        lookup ((G, D, U, s), (!table), [])
      end

   (* ---------------------------------------------------------------------- *)
   (* TOP LEVEL *)

    fun reset () = (table := [])


    fun solutions {solutions = S, lookup = i} = S
    fun lookup {solutions = S, lookup = i} = i


    fun (* GEN BEGIN FUN FIRST *) noAnswers [] = true (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) noAnswers ((H as ((G', D', U'), answ))::L') =
          case (List.take (solutions(answ), lookup(answ)))
            of [] => noAnswers L'
          | L  => false (* GEN END FUN BRANCH *)


    fun callCheck (G, D, U) =
          case (!strategy) of
            Variant => callCheckVariant (G, D, U)
          | Subsumption => callCheckSubsumes (G, D, U)

    fun answCheck (G, D, U, s, O) =
      case (!strategy) of
        Variant => answCheckVariant (G, D, U, s, O)
      | Subsumption => answCheckSubsumes (G, D, U, s, O)


    (* needs to take into account previous size of table *)
    fun updateTable () =
          let
            fun (* GEN BEGIN FUN FIRST *) update [] T Flag = (Flag, T) (* GEN END FUN FIRST *)
              | (* GEN BEGIN FUN BRANCH *) update (((k, G, D, U), {solutions = S, lookup = i})::T) T' Flag =
              let
                (* GEN BEGIN TAG OUTSIDE LET *) val l = length(S) (* GEN END TAG OUTSIDE LET *)
              in
                if (l = i) then
                  (* no new solutions were added in the previous stage *)
                  update T (((k, G, D, U), {solutions = S, lookup = List.length(S)})::T') Flag
                else
                  (* new solutions were added *)
                  update T (((k, G, D, U), {solutions = S, lookup = List.length(S)})::T') true
              end (* GEN END FUN BRANCH *)
            (* GEN BEGIN TAG OUTSIDE LET *) val (Flag, T) = update (!table) [] false (* GEN END TAG OUTSIDE LET *)
            (* GEN BEGIN TAG OUTSIDE LET *) val r = Flag orelse (!added) (* GEN END TAG OUTSIDE LET *)
          in
            added := false;
            table := rev(T);
            (* in each stage incrementally increase termDepth *)
    (*          termDepth := (!termDepth +1); *)
            r
          end

  in

(*  val termDepth = termDepth
    val ctxDepth = ctxDepth
    val ctxLength = ctxLength
*)
    (* GEN BEGIN TAG OUTSIDE LET *) val table = table (* GEN END TAG OUTSIDE LET *)
    (* GEN BEGIN TAG OUTSIDE LET *) val solutions = solutions (* GEN END TAG OUTSIDE LET *)
    (* GEN BEGIN TAG OUTSIDE LET *) val lookup = lookup (* GEN END TAG OUTSIDE LET *)
    (* GEN BEGIN TAG OUTSIDE LET *) val noAnswers = noAnswers (* GEN END TAG OUTSIDE LET *)

    (* GEN BEGIN TAG OUTSIDE LET *) val reset = reset (* GEN END TAG OUTSIDE LET *)

    (* GEN BEGIN TAG OUTSIDE LET *) val printTable = printTable (* GEN END TAG OUTSIDE LET *)
    (* GEN BEGIN TAG OUTSIDE LET *) val printTableEntries = printTableEntries (* GEN END TAG OUTSIDE LET *)

    (* GEN BEGIN TAG OUTSIDE LET *) val callCheck = callCheck (* GEN END TAG OUTSIDE LET *)
    (* GEN BEGIN TAG OUTSIDE LET *) val answerCheck = answCheck (* GEN END TAG OUTSIDE LET *)

    (* GEN BEGIN TAG OUTSIDE LET *) val updateTable = updateTable (* GEN END TAG OUTSIDE LET *)


  end (* local *)

end (* GEN END FUNCTOR DECL *);  (* functor TableIndex *)

