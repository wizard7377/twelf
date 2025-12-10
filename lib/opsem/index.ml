(* Indexing for table *)
(* Author: Brigitte Pientka *)

module TableIndex (Global : GLOBAL)
   (Queue : QUEUE)
                    (*! module IntSyn' : INTSYN !*)
                    (*! module CompSyn': COMPSYN !*)
                    (*! sharing CompSyn'.IntSyn = IntSyn' !*)
                    (Subordinate : SUBORDINATE)
                    (*! sharing Subordinate.IntSyn = IntSyn'                   !*)
                    module Conv: CONV
                    (*! sharing Conv.IntSyn = IntSyn' !*)
                    (Unify : UNIFY)
                    (*! sharing Unify.IntSyn = IntSyn' !*)
                    (AbstractTabled : ABSTRACTTABLED)
                    (*! sharing AbstractTabled.IntSyn = IntSyn' !*)
                    (Whnf : WHNF)
                    (*! sharing Whnf.IntSyn = IntSyn' !*)
                    (Print : PRINT)
                    (*! sharing Print.IntSyn = IntSyn' !*)
                    (CPrint : CPRINT)
                    (*! sharing CPrint.IntSyn = IntSyn' !*)
                    (*! sharing CPrint.CompSyn = CompSyn' !*)
                    (Names : NAMES)
                    (*! sharing Names.IntSyn = IntSyn' !*)
                    (TypeCheck : TYPECHECK): TABLEINDEX =
                    (*! sharing TypeCheck.IntSyn = IntSyn' !*)
struct
  (*! module IntSyn = IntSyn' !*)
  (*! module CompSyn = CompSyn' !*)
  module Conv = Conv


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

  type answer = {solutions : ((IntSyn.dctx * IntSyn.Sub) * CompSyn.pskeleton) list,
                 lookup: int}

  (* entry = (((i, G, D, U), A)) where i is the access counter
   *)
  type entry = (((int ref * IntSyn.dctx * IntSyn.dctx * IntSyn.exp) * answer))

  type entries = entry list

  type index = entry list

  type answstate = New | Repeated

  type strategy = Variant | Subsumption

  let added = ref false;

  (* ---------------------------------------------------------------------- *)
  (* global search parameters *)

  let strategy  = ref Variant (* Subsumption *) (* Variant *)

  (* term abstraction after term depth is greater than 5 *)
  let termDepth = ref NONE : int option ref;
  let ctxDepth = ref NONE : int option ref;
  let ctxLength = ref NONE : int option ref;

(*   let termDepth = ref (!globalTermDepth); *)
(*   let ctxDepth = ref (!globalCtxDepth);   *)
(*   let ctxLength = ref (!globalCtxLength); *)

  (* apply strengthening during abstraction *)
  let strengthen = AbstractTabled.strengthen ;

  (* original query *)
  let query : (IntSyn.dctx * IntSyn.dctx  * IntSyn.exp * IntSyn.Sub * (CompSyn.pskeleton -> unit))
                option ref = ref NONE

  (* ---------------------------------------------------------------------- *)

  local
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
    let rec concat = function (I.Null, G') -> G'
      | (I.Decl(G, D), G') -> I.Decl(concat(G,G'), D)



   let rec reverse = function (I.Null, G') -> G'
     | (I.Decl(G, D), G') -> 
         reverse (G, I.Decl(G', D))

    (* ---------------------------------------------------------------------- *)

    (* printTable () = () *)

    let rec printTable () =
      let
        let rec proofTerms (G, D, U, []) = print ""
          | proofTerms (G, D, U, (((D', s'), _)::S)) =
          ((* (print (Print.expToString (I.Null,  *)
(*              A.raiseType(Names.ctxName(concat(G,D')), I.EClo(U, s')))) *)

           (print (Print.expToString (I.Null, A.raiseType(Names.ctxName(D'),
                        I.EClo(A.raiseType(Names.ctxName(G), U), s'))))
            handle _ => print "EXCEPTION" );
           (* do not print pskeletons *)
           print ", \n\t";
           proofTerms (G, D, U, S))

        let rec printT = function [] -> ()
          | (((k, G, D, U), {solutions -> S, lookup = i})::T) =
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
                              print (" ] -- lookup : " ^ Int.toString i ^ "\n\n"))
      in
        print ("Table: \n");
        printT (!table);
        print ("End Table \n");
        print ("Number of table entries   : " ^ Int.toString(length(!table)) ^ "\n")
      end


    (* printTableEntries () = () *)

    let rec printTableEntries () =
      let
        let rec printT = function [] -> ()
          | (((k, G, D, U), {solutions -> S, lookup = i})::T) =
          (printT T ;
           print (Print.expToString (I.Null,
                                     A.raiseType(concat(G, D), U)) ^ "\n Access Counter : " ^ (Int.toString (!k)) ^ " \n"))
      in
        print ("TableEntries: \n");
        printT (!table);
        print ("End TableEntries \n");
        print ("Number of table entries   : " ^ Int.toString(length(!table)) ^ "\n")
      end


    (* ---------------------------------------------------------------------- *)

    (* Term Abstraction *)

    let rec lengthSpine = function (I.Nil) -> 0
      | (I.SClo(S, s')) -> 1 + lengthSpine(S)


    let rec exceedsTermDepth (i) =
      case (!termDepth) of
        NONE => false
      | SOME(n) => (i > n)

    let rec exceedsCtxDepth (i) =
      case (!ctxDepth) of
        NONE => false
      | SOME(n) => (print ("\n exceedsCtxDepth " ^Int.toString i ^ " > " ^ Int.toString n ^ " ? ") ;(i > n))

    let rec exceedsCtxLength (i) =
      case (!ctxLength) of
        NONE => false
      | SOME(n) => (i > n)

    let rec max (x,y) =
      if x > y then x
      else y

    let rec oroption = function (NONE, NONE, NONE) -> false
      | (SOME(k), _ , _) -> true
      | (_ , SOME(n), _) -> true
      | (_ , _, SOME(n)) -> true

    let rec abstractionSet () =
      oroption(!termDepth, !ctxDepth, !ctxLength)

    (* countDepth U =
         ctr = (ctrTerm, ctrDecl, ctrLength)
         ctrTerm : max term depth
         ctrDecl : max type depth in decl
         ctrLength : length of decl

    *)

    let rec exceeds (U) = countDecl(0,0, U)

    and countDecl (ctrType, ctrLength, I.Pi((D, _), V)) =
         let
           let ctrType' = countDec(0, D)
(*         let _ = print ("\n ctrType' = " ^ Int.toString ctrType')  *)
         in
           if ctrType' > ctrType then
             countDecl (ctrType', ctrLength + 1, V)
           else
             countDecl (ctrType, ctrLength + 1, V)
         end
      | countDecl(ctrType, ctrLength, U) =
         let
           let ctrTerm = count (0, U)
(*         let _ = print ("\n 1 ctrTerm = " ^ Int.toString ctrTerm)
           let _ = print ("\n 1 ctxLength = " ^ Int.toString ctrLength)
           let _ = print ("\n 1 ctxDepth = " ^ Int.toString ctrType)
*)
         in
           exceedsCtxDepth(ctrType) orelse
           exceedsCtxLength(ctrLength) orelse
           exceedsTermDepth(count(0,U))
         end

    and countDec (ctr, I.Dec(_, U)) = count(ctr, U)
      | countDec (ctr, I.BDec(_,s)) = 0

    and count (ctr, (U as I.Uni (L))) = ctr
      | count (ctr, I.Pi((D, _), V)) =
          let
            let ctrTerm = count (ctr, V)
            let ctrType = countDec (ctr, D)
(*         let _ = print ("\n ctrTerm = " ^ Int.toString ctrTerm)
           let _ = print ("\n ctrType = " ^ Int.toString ctrType)
*)

          in
          max(ctrType,ctrTerm) (* to revise ?*)
          end
      | count (ctr, I.Root (F, S)) =
         let
           let ctrDepth = countSpine (1, S)
(*         let _ = print ("\n spineDepth = " ^ Int.toString ctrDepth)
           let _ = print ("\n RootF = " ^ Int.toString(ctrDepth + ctr))
*)
         in
           (ctrDepth + 1 + ctr)
(*         (ctrLength + ctr) *)
         end
      | count (ctr, I.Redex (U, S)) =
         let
           let ctrDepth = count (0, U)
           let ctrDepth' =  countSpine (ctrDepth, S)
(*         let _ = print ("\n SpindeDepth = " ^ Int.toString ctrDepth)
           let _ = print ("\n Redex = " ^ Int.toString(max(ctrDepth',ctrDepth) + ctr))*)

         in
           (max(ctrDepth',ctrDepth) + ctr)
         end
      | count (ctr, I.Lam (D, U)) =
         count (ctr+1, U)
      | count (ctr, (X as I.EVar _)) =
         (* shouldn't happen *)
         ctr
      | count (ctr, I.EClo(E, s)) =
         count (ctr, E)
      | count (ctr, (F as I.FgnExp (cs, ops))) =
         (* shouldn't happen *)
         (ctr)

 (* count max depth of term in S + length of S *)
    and countSpine (ctrDepth, I.Nil)  = ctrDepth
      | countSpine (ctr, I.SClo (S, s')) =
         (* ? *)
         countSpine (ctr, S)
      | countSpine (ctrDepth, I.App (U, S)) =
         let
           let ctrDepth' = count (0, U)
         in
           countSpine (max(ctrDepth', ctrDepth), S)
      end



   (* ---------------------------------------------------------------------- *)
   (* reinstSub (G, D, s) = s'
    *
    * If D', G |- s : D, G
    * then  G |- s' : D, G
    *)

   let rec reinstSub = function (G, I.Null, s) -> s
      | (G, I.Decl(D, I.Dec(_,A)), s) -> 
      let
        let X = I.newEVar (I.Null, A)
      in
        I.Dot(I.Exp(X), reinstSub (G, D, s))

      end


   (* ---------------------------------------------------------------------- *)
   (* variant (U,s) (U',s')) = bool   *)

    let rec variant (Us, Us') = Conv.conv (Us, Us')

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
    let rec subsumes ((G, D, U), (G', D', U')) =
      let
        let Upi = A.raiseType (G, U)
        let Upi' = A.raiseType (G', U')
        let s' = reinstSub (G', D', I.id)
      in
        CSManager.trail (fn () =>
                         Unify.unifiable (D, (Upi', s'), (Upi, I.id)))
      end


    let rec equalSub (I.Shift k, I.Shift k') = (k = k')
      | equalSub (I.Dot(F, S), I.Dot(F', S')) =
        equalFront (F, F') andalso equalSub (S, S')
      | equalSub (I.Dot(F,S), I.Shift k) = false
      | equalSub (I.Shift k, I.Dot(F,S)) = false

    and equalFront (I.Idx n, I.Idx n') = (n = n')
      | equalFront (I.Exp U, I.Exp V) = Conv.conv ((U, I.id), (V, I.id))
      | equalFront (I.Undef, I.Undef) = true

    let rec equalSub1 (I.Dot(ms, s), I.Dot(ms', s')) =
          equalSub (s, s')


    let rec equalCtx (I.Null, I.Null) = true
      | equalCtx (I.Decl(Dk, I.Dec(_, A)), I.Decl(D1, I.Dec(_, A1))) =
        Conv.conv ((A, I.id), (A1, I.id)) andalso equalCtx(Dk, D1)

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

    let rec callCheckVariant (G, D, U) =
      let
        let Upi = A.raiseType(concat(G, D), U)
        let rec lookup ((G, D, U), []) =
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
                NONE)
          | lookup ((G, D, U), ((H as ((k, G', D', U'), answ))::T)) =
            if variant ((Upi, I.id), (A.raiseType(concat(G',D'), U'), I.id)) then
              (k := !k+1;
               (if (!Global.chatter) >= 5 then
                  print ("call " ^ Print.expToString (I.Null, Upi) ^ " found in table \n ")
                else
                  ());
                  SOME[((G', D', U'), answ)])
            else
              lookup ((G, D, U), T)
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


    let rec callCheckSubsumes (G, D, U) =
      let
        let rec lookup ((G, D, U), []) =
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
                NONE)
          | lookup ((G, D, U), (((k, G', D', U'), answ)::T)) =
            if (subsumes ((G, D, U), (G', D', U'))) then
              ((if (!Global.chatter) >= 5 then
                 print ("call " ^ Print.expToString (I.Null, A.raiseType(concat(G, D), U)) ^ "found in table \n ")
               else
                 ());
                  k := !k+1;
                 SOME([((G', D', U'), answ)]))
            else
              lookup ((G, D, U), T)
      in
        lookup ((G, D, U), (!table))
      end

    (* ---------------------------------------------------------------------- *)
    let rec member ((Dk, sk), []) = false
      | member ((Dk, sk), (((D1, s1),_)::S)) =
      (* do we really need to compare Gus and Gs1 ?  *)
      if equalSub (sk,s1) andalso equalCtx (Dk, D1) then
        true
      else
        member ((Dk, sk), S)

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
    let rec answCheckVariant (G, D, U, s, O) =
      let
        let Upi = A.raiseType(concat(G, D), U)

        let _ = if (!Global.chatter) >= 5 then
                  (print "\n AnswCheckInsert: ";
                   print (Print.expToString(I.Null,
                                            I.EClo(A.raiseType(G, U),s)) ^ "\n");
                   print "\n Table Index : " ;
                   print (Print.expToString (I.Null,  Upi) ^ "\n"))
                else
                  ()

        let rec lookup  (G, D, U, s) [] T =
          (* cannot happen ! *)
          (print (Print.expToString(I.Null, I.EClo(A.raiseType(G,U),s))
                  ^ " call should always be already in the table !\n") ;
           Repeated)
          | lookup (G, D, U, s) ((H as ((k, G', D',U'),
                    {solutions = S, lookup = i}))::T) T' =
          if variant ((Upi, I.id),
                      (A.raiseType(concat(G', D'), U'), I.id))
            then
              let
                let (Dk, sk) = A.abstractAnswSub s
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
              lookup (G, D, U, s) T (H::T')
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

    let rec memberSubsumes = function ((G, D, U, s), (G', U', [])) -> false
      | ((G, D, U, s), (G', U', (((D1, s1), _)::A))) -> 
        let
          let Upi = A.raiseType(G, U)
          let Upi' = A.raiseType(G',U')
          let s1' = reinstSub (G', D1, I.id)
          let Vpis = (I.EClo(Upi', s1), s1')

          (* assume G' and G are the same for now *)
          let b = CSManager.trail (fn () =>
                                   Unify.unifiable (D, (Upi, s), (Vpis)))
        in
          if b then
            ((if (!Global.chatter) >= 5 then
                print "\n answer in table subsumes answer \n "
              else
                ());
             true)
          else
            memberSubsumes ((G, D, U, s), (G', U', A))
        end

  let rec shift = function (0, s) -> s
    | (n, s) -> shift(n-1, I.dot1 s)


   let rec answCheckSubsumes (G, D, U, s, O) =
      let
        let Upi = A.raiseType(G, U)
        let _ = if (!Global.chatter) >= 4 then
                    (print ("\n AnswCheckInsert (subsumes): " );
                     print(Print.expToString(I.Null, I.EClo(Upi, s))
                       ^ "\n"))
                else ()

        let rec lookup ((G, D, U , s), [], T) =
          (* cannot happen ! *)
          (print (Print.expToString(concat(G, D), I.EClo(U,s))
                  ^ " call should always be already in the table !\n") ;
           Repeated)
          | lookup ((G, D, U, s), (((k, G', D', U'), {solutions = A, lookup = i})::T), T') =
          if (subsumes ((G, D, U), (G', D', U'))) then
            let
              let (Dk, sk) = A.abstractAnswSub s
             in
               if memberSubsumes ((G, Dk, U, sk), (G', U', A)) then
                 Repeated
               else
                 let
                   let s' = reinstSub (G', D', I.id)
                   let _ = if (!Global.chatter) >= 4 then
                            (print "\n new answer to be added to Index \n";
                             print (Print.expToString(I.Null,
                                                    A.raiseType(concat(G', D'), U')) ^"\n");
                             print "\n answer added \n";
                             print (Print.expToString(I.Null, A.raiseType(Dk,
                                        I.EClo(A.raiseType(G, U), sk))) ^ "\n"))
                           else
                             ()
                   (*  higher-order matching *)
                   let _ = if (Unify.unifiable (Dk, (A.raiseType(G, U), sk),
                                               (A.raiseType(G', U'), s')))
                             then (if (!Global.chatter) >= 4 then
                                     (print "\n1 unification successful !\n";
                                      print (Print.expToString(I.Null, A.raiseType(Dk,
                                              I.EClo(A.raiseType(G', U'), s')))
                                             ^ "\n"))
                                   else
                                     ())
                           else print "\n1 unification failed! -- should never happen ?"
                   let (Dk', sk') = A.abstractAnsw (Dk, s')
                   let rs = reinstSub (G', Dk', I.id) (* reinstantiate us' *)
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
                         CSManager.trail (fn () =>
                             (if Unify.unifiable (D1, (A.raiseType(G1, U1), s1),
                                                  (I.EClo(A.raiseType(G', U'), sk'), rs))
                                then
                                  let
                                    let w = if (!strengthen)
                                              then
                                                Subordinate.weaken (I.Null, IntSyn.targetFam(I.EClo(U1, s1)))
                                            else
                                              I.id
                                  in
                                                 (* (I.EClo(N1, I.comp(shift(I.ctxLength(Gdp1),s1), w))) *)
                                                 sc1 O
                                               end
                                           else ()
                                             ))
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
            lookup ((G, D, U, s), T, (((k, G', D', U'), {solutions = A, lookup = i})::T'))
      in
        lookup ((G, D, U, s), (!table), [])
      end

   (* ---------------------------------------------------------------------- *)
   (* TOP LEVEL *)

    let rec reset () = (table := [])


    let rec solutions {solutions = S, lookup = i} = S
    let rec lookup {solutions = S, lookup = i} = i


    let rec noAnswers = function [] -> true
      | ((H as ((G', D', U'), answ))::L') -> 
          case (List.take (solutions(answ), lookup(answ)))
            of [] => noAnswers L'
          | L  => false


    let rec callCheck (G, D, U) =
          case (!strategy) of
            Variant => callCheckVariant (G, D, U)
          | Subsumption => callCheckSubsumes (G, D, U)

    let rec answCheck (G, D, U, s, O) =
      case (!strategy) of
        Variant => answCheckVariant (G, D, U, s, O)
      | Subsumption => answCheckSubsumes (G, D, U, s, O)


    (* needs to take into account previous size of table *)
    let rec updateTable () =
          let
            let rec update = function [] T Flag -> (Flag, T)
              | (((k, G, D, U), {solutions -> S, lookup = i})::T) T' Flag =
              let
                let l = length(S)
              in
                if (l = i) then
                  (* no new solutions were added in the previous stage *)
                  update T (((k, G, D, U), {solutions = S, lookup = List.length(S)})::T') Flag
                else
                  (* new solutions were added *)
                  update T (((k, G, D, U), {solutions = S, lookup = List.length(S)})::T') true
              end
            let (Flag, T) = update (!table) [] false
            let r = Flag orelse (!added)
          in
            added := false;
            table := rev(T);
            (* in each stage incrementally increase termDepth *)
(*          termDepth := (!termDepth +1); *)
            r
          end

  in

(*  let termDepth = termDepth
    let ctxDepth = ctxDepth
    let ctxLength = ctxLength
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


  end (* local *)

end;; (* functor TableIndex *)

