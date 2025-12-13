(* Meta Prover Interface *)
(* Author: Carsten Schuermann *)

functor (* GEN BEGIN FUNCTOR DECL *) Mpi (structure MetaGlobal : METAGLOBAL
             structure MetaSyn' : METASYN
             structure Init : INIT
             sharing Init.MetaSyn = MetaSyn'
             structure Filling : FILLING
             sharing Filling.MetaSyn = MetaSyn'
             structure Splitting : SPLITTING
             sharing Splitting.MetaSyn = MetaSyn'
             structure Recursion : RECURSION
             sharing Recursion.MetaSyn = MetaSyn'
             structure Lemma : LEMMA
             sharing Lemma.MetaSyn = MetaSyn'
             structure Strategy : STRATEGY
             sharing Strategy.MetaSyn = MetaSyn'
             structure Qed : QED
             sharing Qed.MetaSyn = MetaSyn'
             structure MetaPrint : METAPRINT
             sharing MetaPrint.MetaSyn = MetaSyn'
             structure Names : NAMES
             (*! sharing Names.IntSyn = MetaSyn'.IntSyn !*)
             structure Timers : TIMERS
             structure Ring : RING)
  : MPI =
struct
  structure MetaSyn = MetaSyn'

  exception Error of string

  local
    structure M = MetaSyn
    structure I = IntSyn

    datatype menu_item =
      Filling of Filling.operator
    | Recursion of Recursion.operator
    | Splitting of Splitting.operator

    (* GEN BEGIN TAG OUTSIDE LET *) val Open : MetaSyn.state Ring.ring ref = ref (Ring.init []) (* GEN END TAG OUTSIDE LET *)
    (* GEN BEGIN TAG OUTSIDE LET *) val Solved : MetaSyn.state Ring.ring ref = ref (Ring.init []) (* GEN END TAG OUTSIDE LET *)
    (* GEN BEGIN TAG OUTSIDE LET *) val History : (MetaSyn.state Ring.ring * MetaSyn.state Ring.ring) list ref = ref nil (* GEN END TAG OUTSIDE LET *)
    (* GEN BEGIN TAG OUTSIDE LET *) val Menu : menu_item list option ref = ref NONE (* GEN END TAG OUTSIDE LET *)

    fun initOpen () = Open := Ring.init [];
    fun initSolved () = Solved := Ring.init [];
    fun empty () = Ring.empty (!Open)
    fun current () = Ring.current (!Open)
    fun delete () = Open := Ring.delete (!Open)
    fun insertOpen S = Open := Ring.insert (!Open, S)
    fun insertSolved S = Solved := Ring.insert (!Solved, S)

    fun insert S =
        if Qed.subgoal S then
          (insertSolved S;
           print (MetaPrint.stateToString S);
           print "\n[Subgoal finished]\n";
           print "\n")
        else insertOpen S

    fun collectOpen () = Ring.foldr op:: nil (!Open)
    fun collectSolved () = Ring.foldr op:: nil (!Solved)
    fun nextOpen () = Open := Ring.next (!Open)

    fun pushHistory () =
          History :=  (!Open, !Solved) :: (!History)
    fun popHistory () =
        case (!History)
          of nil => raise Error "History stack empty"
           | (Open', Solved') :: History' =>
             (History := History';
              Open := Open';
              Solved := Solved')


    fun abort s =
        (print ("* " ^ s);
         raise Error s)

    fun reset () =
        (initOpen ();
         initSolved ();
         History := nil;
         Menu := NONE)

    fun (* GEN BEGIN FUN FIRST *) cLToString (nil) = "" (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) cLToString (c :: nil) =
          (I.conDecName (I.sgnLookup c)) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) cLToString (c :: L) =
          (I.conDecName (I.sgnLookup c)) ^ ", " ^ (cLToString L) (* GEN END FUN BRANCH *)

    fun (* GEN BEGIN FUN FIRST *) SplittingToMenu (nil, A) = A (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) SplittingToMenu (O :: L, A) = SplittingToMenu (L, Splitting O :: A) (* GEN END FUN BRANCH *)

    fun (* GEN BEGIN FUN FIRST *) FillingToMenu (nil, A) = A (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) FillingToMenu (O :: L, A) = FillingToMenu (L, Filling O :: A) (* GEN END FUN BRANCH *)

    fun (* GEN BEGIN FUN FIRST *) RecursionToMenu (nil, A) = A (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) RecursionToMenu (O :: L, A) = RecursionToMenu (L, Recursion O :: A) (* GEN END FUN BRANCH *)

    fun menu () =
        if empty () then Menu := NONE
        else
          let
            (* GEN BEGIN TAG OUTSIDE LET *) val S = current () (* GEN END TAG OUTSIDE LET *)
            (* GEN BEGIN TAG OUTSIDE LET *) val SplitO = Splitting.expand S (* GEN END TAG OUTSIDE LET *)
            (* GEN BEGIN TAG OUTSIDE LET *) val  RecO = Recursion.expandEager S (* GEN END TAG OUTSIDE LET *)
            (* GEN BEGIN TAG OUTSIDE LET *) val (FillO, FillC) = Filling.expand S (* GEN END TAG OUTSIDE LET *)
          in
            Menu := SOME (FillingToMenu ([FillC],
                          FillingToMenu (FillO,
                                         RecursionToMenu (RecO,
                                                          SplittingToMenu (SplitO, nil)))))
          end


    fun format k =
        if k < 10 then (Int.toString k) ^ ".  "
        else (Int.toString k) ^ ". "

    fun menuToString () =
        let
          fun (* GEN BEGIN FUN FIRST *) menuToString' (k, nil) = "" (* GEN END FUN FIRST *)
            | (* GEN BEGIN FUN BRANCH *) menuToString' (k, Splitting O :: M) =
                (menuToString' (k+1, M)) ^ "\n" ^ (format k) ^ (Splitting.menu O) (* GEN END FUN BRANCH *)
            | (* GEN BEGIN FUN BRANCH *) menuToString' (k, Filling O :: M) =
                (menuToString' (k+1, M)) ^ "\n" ^ (format k) ^ (Filling.menu O) (* GEN END FUN BRANCH *)
            | (* GEN BEGIN FUN BRANCH *) menuToString' (k, Recursion O :: M) =
                (menuToString' (k+1, M)) ^ "\n" ^ (format k) ^ (Recursion.menu O) (* GEN END FUN BRANCH *)
        in
          case !Menu of
            NONE => raise Error "Menu is empty"
          | SOME M => menuToString' (1, M)
        end


    fun makeConDec (M.State (name, M.Prefix (G, M, B), V)) =
        let
          fun (* GEN BEGIN FUN FIRST *) makeConDec' (I.Null, V, k) = I.ConDec (name, NONE, k, I.Normal, V, I.Type) (* GEN END FUN FIRST *)
            | (* GEN BEGIN FUN BRANCH *) makeConDec' (I.Decl (G, D), V, k) =
              makeConDec' (G, I.Pi ((D, I.Maybe), V), k+1) (* GEN END FUN BRANCH *)
        in
          (makeConDec' (G, V, 0))
        end

    fun (* GEN BEGIN FUN FIRST *) makeSignature (nil) = M.SgnEmpty (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) makeSignature (S :: SL) =
          M.ConDec (makeConDec S,
                      makeSignature SL) (* GEN END FUN BRANCH *)
    fun extract () =
        if empty () then makeSignature (collectSolved ())
        else (print "[Error: Proof not completed yet]\n"; M.SgnEmpty)

    fun show () =
        print (MetaPrint.sgnToString (extract ()) ^ "\n")

    fun printMenu () =
        if empty () then (show (); print "[QED]\n")
        else
          let
            (* GEN BEGIN TAG OUTSIDE LET *) val S = current () (* GEN END TAG OUTSIDE LET *)
          in
            (print "\n";
             print (MetaPrint.stateToString S);
             print "\nSelect from the following menu:\n";
             print (menuToString ());
             print "\n")
          end


    fun (* GEN BEGIN FUN FIRST *) contains (nil, _) = true (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) contains (x :: L, L') =
          (List.exists ((* GEN BEGIN FUNCTION EXPRESSION *) fn x' => x = x' (* GEN END FUNCTION EXPRESSION *)) L') andalso contains (L, L') (* GEN END FUN BRANCH *)

    fun equiv (L1, L2) =
          contains (L1, L2) andalso contains (L2, L1)

    fun init' (k, cL as (c :: _)) =
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val _ = MetaGlobal.maxFill := k (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val _ = reset () (* GEN END TAG OUTSIDE LET *);
          (* GEN BEGIN TAG OUTSIDE LET *) val cL' = Order.closure c
            handle Order.Error _ => cL (* GEN END TAG OUTSIDE LET *)  (* if no termination ordering given! *)
        in
          if equiv (cL, cL') then
            map ((* GEN BEGIN FUNCTION EXPRESSION *) fn S => insert S (* GEN END FUNCTION EXPRESSION *)) (Init.init cL)
          else raise Error ("Theorem by simultaneous induction not correctly stated:"
                             ^ "\n            expected: " ^ (cLToString cL'))
        end

    fun init (k, nL) =
        let
          fun (* GEN BEGIN FUN FIRST *) cids nil = nil (* GEN END FUN FIRST *)
            | (* GEN BEGIN FUN BRANCH *) cids (name :: nL) =
              (case Names.stringToQid name
                 of NONE => raise Error ("Malformed qualified identifier " ^ name)
                  | SOME qid =>
              (case Names.constLookup qid
                 of NONE => raise Error ("Type family " ^ Names.qidToString qid ^ " not defined")
                  | SOME cid => cid :: (cids nL))) (* GEN END FUN BRANCH *)
        in
          ((init' (k, cids nL); menu (); printMenu ())
            handle Splitting.Error s => abort ("Splitting Error: " ^ s)
                 | Filling.Error s => abort ("Filling Error: " ^ s)
                 | Recursion.Error s => abort ("Recursion Error: " ^ s)
                 | Error s => abort ("Mpi Error: " ^ s))
        end

    fun select k =
        let
          fun (* GEN BEGIN FUN FIRST *) select' (k, nil) = abort ("No such menu item") (* GEN END FUN FIRST *)
            | (* GEN BEGIN FUN BRANCH *) select' (1, Splitting O :: _) =
                let
                  (* GEN BEGIN TAG OUTSIDE LET *) val S' = (Timers.time Timers.splitting Splitting.apply) O (* GEN END TAG OUTSIDE LET *)
                  (* GEN BEGIN TAG OUTSIDE LET *) val _ = pushHistory () (* GEN END TAG OUTSIDE LET *)
                  (* GEN BEGIN TAG OUTSIDE LET *) val _ = delete () (* GEN END TAG OUTSIDE LET *)
                  (* GEN BEGIN TAG OUTSIDE LET *) val _ = map insert S' (* GEN END TAG OUTSIDE LET *)
                in
                  (menu (); printMenu ())
                end (* GEN END FUN BRANCH *)
            | (* GEN BEGIN FUN BRANCH *) select' (1, Recursion O :: _) =
                let
                  (* GEN BEGIN TAG OUTSIDE LET *) val S' = (Timers.time Timers.recursion Recursion.apply) O (* GEN END TAG OUTSIDE LET *)
                  (* GEN BEGIN TAG OUTSIDE LET *) val _ = pushHistory () (* GEN END TAG OUTSIDE LET *)
                  (* GEN BEGIN TAG OUTSIDE LET *) val _ = delete () (* GEN END TAG OUTSIDE LET *)
                  (* GEN BEGIN TAG OUTSIDE LET *) val _ = insert S' (* GEN END TAG OUTSIDE LET *)
                in
                  (menu (); printMenu ())
                end (* GEN END FUN BRANCH *)
            | (* GEN BEGIN FUN BRANCH *) select' (1, Filling O :: _) =
                let
                  (* GEN BEGIN TAG OUTSIDE LET *) val _ =
                    case (Timers.time Timers.filling Filling.apply) O of
                      nil => abort ("Filling unsuccessful: no object found")
                    | (S :: _) => (delete ();
                                   insert S;
                                   pushHistory ()) (* GEN END TAG OUTSIDE LET *)
                in
                  (menu (); printMenu ())
                end (* GEN END FUN BRANCH *)
            | (* GEN BEGIN FUN BRANCH *) select' (k, _ :: M) = select' (k-1, M) (* GEN END FUN BRANCH *)
        in
          (case !Menu of
            NONE => raise Error "No menu defined"
          | SOME M => select' (k, M))
             handle Splitting.Error s => abort ("Splitting Error: " ^ s)
                  | Filling.Error s => abort ("Filling Error: " ^ s)
                  | Recursion.Error s => abort ("Recursion Error: " ^ s)
                  | Error s => abort ("Mpi Error: " ^ s)
        end


    fun lemma name =
        if empty () then raise Error "Nothing to prove"
        else
          let
            (* GEN BEGIN TAG OUTSIDE LET *) val S = current () (* GEN END TAG OUTSIDE LET *)
            (* GEN BEGIN TAG OUTSIDE LET *) val S' = Lemma.apply (S, valOf (Names.constLookup (valOf (Names.stringToQid name))))
              handle Splitting.Error s => abort ("Splitting Error: " ^ s)
                   | Filling.Error s => abort ("Filling Error: " ^ s)
                   | Recursion.Error s => abort ("Recursion Error: " ^ s)
                   | Error s => abort ("Mpi Error: " ^ s) (* GEN END TAG OUTSIDE LET *)
            (* GEN BEGIN TAG OUTSIDE LET *) val _ = pushHistory () (* GEN END TAG OUTSIDE LET *)
            (* GEN BEGIN TAG OUTSIDE LET *) val _ = delete () (* GEN END TAG OUTSIDE LET *)
            (* GEN BEGIN TAG OUTSIDE LET *) val _ = insert S' (* GEN END TAG OUTSIDE LET *)
          in
            (menu (); printMenu ())
          end

    fun solve () =
        if empty () then raise Error "Nothing to prove"
        else
          let
            (* GEN BEGIN TAG OUTSIDE LET *) val S = current () (* GEN END TAG OUTSIDE LET *)
            (* GEN BEGIN TAG OUTSIDE LET *) val (Open', Solved') = Strategy.run [S]
              handle Splitting.Error s => abort ("Splitting Error: " ^ s)
                   | Filling.Error s => abort ("Filling Error: " ^ s)
                   | Recursion.Error s => abort ("Recursion Error: " ^ s)
                   | Error s => abort ("Mpi Error: " ^ s) (* GEN END TAG OUTSIDE LET *)
            (* GEN BEGIN TAG OUTSIDE LET *) val _ = pushHistory () (* GEN END TAG OUTSIDE LET *)
            (* GEN BEGIN TAG OUTSIDE LET *) val _ = delete () (* GEN END TAG OUTSIDE LET *)
            (* GEN BEGIN TAG OUTSIDE LET *) val _ = map insertOpen Open' (* GEN END TAG OUTSIDE LET *)
            (* GEN BEGIN TAG OUTSIDE LET *) val _ = map insertSolved Solved' (* GEN END TAG OUTSIDE LET *)
          in
            (menu (); printMenu ())
          end

    fun auto () =
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val (Open', Solved') = Strategy.run (collectOpen ())
            handle Splitting.Error s => abort ("Splitting Error: " ^ s)
                 | Filling.Error s => abort ("Filling Error: " ^ s)
                 | Recursion.Error s => abort ("Recursion Error: " ^ s)
                 | Error s => abort ("Mpi Error: " ^ s) (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val _ = pushHistory () (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val _ = initOpen () (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val _ = map insertOpen Open' (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val _ = map insertSolved Solved' (* GEN END TAG OUTSIDE LET *)
        in
          (menu (); printMenu ())
        end

    fun next () = (nextOpen (); menu (); printMenu ())

    fun undo () = (popHistory (); menu (); printMenu ())

  in
    (* GEN BEGIN TAG OUTSIDE LET *) val init = init (* GEN END TAG OUTSIDE LET *)
    (* GEN BEGIN TAG OUTSIDE LET *) val select = select (* GEN END TAG OUTSIDE LET *)
    (* GEN BEGIN TAG OUTSIDE LET *) val print = printMenu (* GEN END TAG OUTSIDE LET *)
    (* GEN BEGIN TAG OUTSIDE LET *) val next = next (* GEN END TAG OUTSIDE LET *)
    (* GEN BEGIN TAG OUTSIDE LET *) val lemma = lemma (* GEN END TAG OUTSIDE LET *)
    (* GEN BEGIN TAG OUTSIDE LET *) val reset = reset (* GEN END TAG OUTSIDE LET *)
    (* GEN BEGIN TAG OUTSIDE LET *) val solve = solve (* GEN END TAG OUTSIDE LET *)
    (* GEN BEGIN TAG OUTSIDE LET *) val auto = auto (* GEN END TAG OUTSIDE LET *)
    (* GEN BEGIN TAG OUTSIDE LET *) val extract = extract (* GEN END TAG OUTSIDE LET *)
    (* GEN BEGIN TAG OUTSIDE LET *) val show = show (* GEN END TAG OUTSIDE LET *)
    (* GEN BEGIN TAG OUTSIDE LET *) val undo = undo (* GEN END TAG OUTSIDE LET *)
 end (* local *)
end (* GEN END FUNCTOR DECL *); (* functor MPI *)
