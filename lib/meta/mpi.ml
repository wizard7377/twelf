(* Meta Prover Interface *)
(* Author: Carsten Schuermann *)

functor (* GEN BEGIN FUNCTOR DECL *) MTPi (structure MTPGlobal : MTPGLOBAL
              (*! structure IntSyn : INTSYN !*)
              (*! structure FunSyn' : FUNSYN !*)
              (*! sharing FunSyn'.IntSyn = IntSyn !*)
              structure StateSyn' : STATESYN
              (*! sharing StateSyn'.IntSyn = IntSyn !*)
              (*! sharing StateSyn'.FunSyn = FunSyn' !*)
              structure RelFun : RELFUN
              (*! sharing RelFun.FunSyn = FunSyn' !*)
              structure Formatter : FORMATTER
              structure Print : PRINT
              (*! sharing Print.IntSyn = IntSyn !*)
                sharing Print.Formatter = Formatter
              structure FunTypeCheck : FUNTYPECHECK
              (*! sharing FunTypeCheck.FunSyn = FunSyn' !*)
                sharing FunTypeCheck.StateSyn = StateSyn'
              structure MTPData : MTPDATA
              structure MTPInit : MTPINIT
              (*! sharing MTPInit.FunSyn = FunSyn' !*)
                sharing MTPInit.StateSyn = StateSyn'
              structure MTPFilling : MTPFILLING
              (*! sharing MTPFilling.FunSyn = FunSyn' !*)
                sharing MTPFilling.StateSyn = StateSyn'
              structure Inference : INFERENCE
              (*! sharing Inference.FunSyn = FunSyn' !*)
                sharing Inference.StateSyn = StateSyn'
              structure MTPSplitting : MTPSPLITTING
                sharing MTPSplitting.StateSyn = StateSyn'
              structure MTPRecursion : MTPRECURSION
                sharing MTPRecursion.StateSyn = StateSyn'
              structure MTPStrategy : MTPSTRATEGY
                sharing MTPStrategy.StateSyn = StateSyn'
              structure MTPrint : MTPRINT
                sharing MTPrint.StateSyn = StateSyn'
              structure Order : ORDER
              (*! sharing Order.IntSyn = IntSyn !*)
              structure Names : NAMES
              (*! sharing Names.IntSyn = IntSyn !*)
              structure Timers : TIMERS
              structure Ring : RING)
  : MTPI =
struct
  exception Error of string

  (*! structure FunSyn = FunSyn' !*)
  structure StateSyn = StateSyn'

  local
    structure I = IntSyn
    structure F = FunSyn
    structure S = StateSyn
    structure Fmt = Formatter

    datatype menu_item =
      Filling of MTPFilling.operator
    | Recursion of MTPRecursion.operator
    | Splitting of MTPSplitting.operator
    | Inference of Inference.operator

    (* GEN BEGIN TAG OUTSIDE LET *) val Open : StateSyn.state Ring.ring ref = ref (Ring.init []) (* GEN END TAG OUTSIDE LET *)
    (* GEN BEGIN TAG OUTSIDE LET *) val Solved : StateSyn.state Ring.ring ref = ref (Ring.init []) (* GEN END TAG OUTSIDE LET *)
    (* GEN BEGIN TAG OUTSIDE LET *) val History : (StateSyn.state Ring.ring * StateSyn.state Ring.ring) list ref = ref nil (* GEN END TAG OUTSIDE LET *)
    (* GEN BEGIN TAG OUTSIDE LET *) val Menu : menu_item list option ref = ref NONE (* GEN END TAG OUTSIDE LET *)

    fun initOpen () = Open := Ring.init [];
    fun initSolved () = Solved := Ring.init [];
    fun empty () = Ring.empty (!Open)
    fun current () = Ring.current (!Open)
    fun delete () = Open := Ring.delete (!Open)
    fun insertOpen S = Open := Ring.insert (!Open, S)
    fun insertSolved S = Solved := Ring.insert (!Solved, S)

    fun insert S = insertOpen S

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


    fun printFillResult (_, P) =
      let
        fun formatTuple (G, P) =
          let
            fun (* GEN BEGIN FUN FIRST *) formatTuple' (F.Unit) = nil (* GEN END FUN FIRST *)
              | (* GEN BEGIN FUN BRANCH *) formatTuple' (F.Inx (M, F.Unit)) =
              [Print.formatExp (G, M)] (* GEN END FUN BRANCH *)
              | (* GEN BEGIN FUN BRANCH *) formatTuple' (F.Inx (M, P')) =
              (Print.formatExp (G, M) ::
               Fmt.String "," :: Fmt.Break :: formatTuple' P') (* GEN END FUN BRANCH *)
          in
            case P
              of (F.Inx (_, F.Unit)) => Fmt.Hbox (formatTuple' P)
              | _ => Fmt.HVbox0 1 1 1
                (Fmt.String "(" :: (formatTuple' P @ [Fmt.String ")"]))
          end
        (* GEN BEGIN TAG OUTSIDE LET *) val S.State (n, (G, B), (IH, OH), d, O, H, F) = current () (* GEN END TAG OUTSIDE LET *)
      in
        TextIO.print ("Filling successful with proof term:\n" ^ (Formatter.makestring_fmt (formatTuple (G, P))) ^ "\n")
      end

    fun (* GEN BEGIN FUN FIRST *) SplittingToMenu (nil, A) = A (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) SplittingToMenu (O :: L, A) = SplittingToMenu (L, Splitting O :: A) (* GEN END FUN BRANCH *)

    fun FillingToMenu (O, A) = Filling O :: A

    fun RecursionToMenu (O, A) = Recursion O :: A

    fun InferenceToMenu (O, A) = Inference O :: A

    fun menu () =
        if empty () then Menu := NONE
        else
          let
            (* GEN BEGIN TAG OUTSIDE LET *) val S = current () (* GEN END TAG OUTSIDE LET *)
            (* GEN BEGIN TAG OUTSIDE LET *) val SplitO = MTPSplitting.expand S (* GEN END TAG OUTSIDE LET *)
            (* GEN BEGIN TAG OUTSIDE LET *) val InfO = Inference.expand S (* GEN END TAG OUTSIDE LET *)
            (* GEN BEGIN TAG OUTSIDE LET *) val RecO = MTPRecursion.expand S (* GEN END TAG OUTSIDE LET *)
            (* GEN BEGIN TAG OUTSIDE LET *) val FillO = MTPFilling.expand S (* GEN END TAG OUTSIDE LET *)
          in
            Menu := SOME (FillingToMenu (FillO,
                                         RecursionToMenu (RecO,
                                                          InferenceToMenu (InfO,
                                                                           SplittingToMenu (SplitO, nil)))))
          end


    fun format k =
        if k < 10 then (Int.toString k) ^ ".  "
        else (Int.toString k) ^ ". "

    fun menuToString () =
        let
          fun (* GEN BEGIN FUN FIRST *) menuToString' (k, nil, (NONE, _)) = (SOME k, "") (* GEN END FUN FIRST *)
            | (* GEN BEGIN FUN BRANCH *) menuToString' (k, nil, (kopt' as SOME _, _)) = (kopt', "") (* GEN END FUN BRANCH *)
            | (* GEN BEGIN FUN BRANCH *) menuToString' (k, Splitting O :: M, kOopt' as (NONE, NONE)) =
              let
                (* GEN BEGIN TAG OUTSIDE LET *) val kOopt'' = if MTPSplitting.applicable O then (SOME k, SOME O)
                              else kOopt' (* GEN END TAG OUTSIDE LET *)
                (* GEN BEGIN TAG OUTSIDE LET *) val (kopt as SOME k'', s) = menuToString' (k+1, M, kOopt'') (* GEN END TAG OUTSIDE LET *)
              in
                (kopt, if k = k'' then s ^ "\n* " ^ (format k) ^ (MTPSplitting.menu O)
                       else s ^ "\n  " ^ (format k) ^ (MTPSplitting.menu O))
              end (* GEN END FUN BRANCH *)
            | (* GEN BEGIN FUN BRANCH *) menuToString' (k, Splitting O :: M, kOopt' as (SOME k', SOME O')) =
              let
                (* GEN BEGIN TAG OUTSIDE LET *) val kOopt'' = if MTPSplitting.applicable O then
                                case MTPSplitting.compare (O, O')
                                  of LESS => (SOME k, SOME O)
                                   | _ => kOopt'
                                else  kOopt' (* GEN END TAG OUTSIDE LET *)
                (* GEN BEGIN TAG OUTSIDE LET *) val (kopt as SOME k'', s) = menuToString' (k+1, M, kOopt'') (* GEN END TAG OUTSIDE LET *)
              in
                (kopt, if  k = k'' then s ^ "\n* " ^ (format k) ^ (MTPSplitting.menu O)
                       else s ^ "\n  " ^ (format k) ^ (MTPSplitting.menu O))
              end (* GEN END FUN BRANCH *)
            | (* GEN BEGIN FUN BRANCH *) menuToString' (k, Filling O :: M, kOopt) =
              let
                (* GEN BEGIN TAG OUTSIDE LET *) val (kopt, s) = menuToString' (k+1, M, kOopt) (* GEN END TAG OUTSIDE LET *)
              in
                (kopt, s ^ "\n  " ^ (format k) ^ (MTPFilling.menu O))
              end (* GEN END FUN BRANCH *)
            | (* GEN BEGIN FUN BRANCH *) menuToString' (k, Recursion O :: M,kOopt) =
              let
                (* GEN BEGIN TAG OUTSIDE LET *) val (kopt, s) = menuToString' (k+1, M, kOopt) (* GEN END TAG OUTSIDE LET *)
              in
                (kopt, s ^ "\n  " ^ (format k) ^ (MTPRecursion.menu O))
              end (* GEN END FUN BRANCH *)
            | (* GEN BEGIN FUN BRANCH *) menuToString' (k, Inference O :: M,kOopt) =
              let
                (* GEN BEGIN TAG OUTSIDE LET *) val (kopt, s) = menuToString' (k+1, M, kOopt) (* GEN END TAG OUTSIDE LET *)
              in
                (kopt, s ^ "\n  " ^ (format k) ^ (Inference.menu O))
              end (* GEN END FUN BRANCH *)
        in
          case !Menu of
            NONE => raise Error "Menu is empty"
          | SOME M =>
              let
                (* GEN BEGIN TAG OUTSIDE LET *) val (kopt, s) = menuToString' (1, M, (NONE, NONE)) (* GEN END TAG OUTSIDE LET *)
              in
                s
              end
        end


    fun printMenu () =
        if empty () then (print "[QED]\n";
                          print ("Statistics: required Twelf.Prover.maxFill := "
                                 ^ (Int.toString (!MTPData.maxFill)) ^ "\n"))
        else
          let
            (* GEN BEGIN TAG OUTSIDE LET *) val S = current () (* GEN END TAG OUTSIDE LET *)
            (* GEN BEGIN TAG OUTSIDE LET *) val _ = if !Global.doubleCheck then FunTypeCheck.isState S else () (* GEN END TAG OUTSIDE LET *)
          in
            (print "\n";
             print (MTPrint.stateToString S);
             print "\nSelect from the following menu:\n";
             print (menuToString ());
             print "\n")
          end


    fun (* GEN BEGIN FUN FIRST *) contains (nil, _) = true (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) contains (x :: L, L') =
          (List.exists ((* GEN BEGIN FUNCTION EXPRESSION *) fn x' => x = x' (* GEN END FUNCTION EXPRESSION *)) L') andalso contains (L, L') (* GEN END FUN BRANCH *)

    fun equiv (L1, L2) =
          contains (L1, L2) andalso contains (L2, L1)

    fun (* GEN BEGIN FUN FIRST *) transformOrder' (G, Order.Arg k) =
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val k' = (I.ctxLength G) -k+1 (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val I.Dec (_, V) = I.ctxDec (G, k') (* GEN END TAG OUTSIDE LET *)
        in
          S.Arg ((I.Root (I.BVar k', I.Nil), I.id), (V, I.id))
        end (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) transformOrder' (G, Order.Lex Os) =
          S.Lex (map ((* GEN BEGIN FUNCTION EXPRESSION *) fn O => transformOrder' (G, O) (* GEN END FUNCTION EXPRESSION *)) Os) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) transformOrder' (G, Order.Simul Os) =
          S.Simul (map ((* GEN BEGIN FUNCTION EXPRESSION *) fn O => transformOrder' (G, O) (* GEN END FUNCTION EXPRESSION *)) Os) (* GEN END FUN BRANCH *)

    fun (* GEN BEGIN FUN FIRST *) transformOrder (G, F.All (F.Prim D, F), Os) =
          S.All (D, transformOrder (I.Decl (G, D), F, Os)) (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) transformOrder (G, F.And (F1, F2), O :: Os) =
          S.And (transformOrder (G, F1, [O]),
                 transformOrder (G, F2, Os)) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) transformOrder (G, F.Ex _, [O]) = transformOrder' (G, O) (* GEN END FUN BRANCH *)

    fun select c = (Order.selLookup c handle _ => Order.Lex [])

    fun init (k, names) =
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val cL = map ((* GEN BEGIN FUNCTION EXPRESSION *) fn x => valOf (Names.constLookup (valOf (Names.stringToQid x))) (* GEN END FUNCTION EXPRESSION *)) names (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val _ = MTPGlobal.maxFill := k (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val _ = reset () (* GEN END TAG OUTSIDE LET *);
          (* GEN BEGIN TAG OUTSIDE LET *) val F = RelFun.convertFor cL (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val O = transformOrder (I.Null, F, map select cL) (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val Slist = MTPInit.init (F, O) (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val _ = if List.length Slist =0 then raise Domain else () (* GEN END TAG OUTSIDE LET *)
        in
          ((map ((* GEN BEGIN FUNCTION EXPRESSION *) fn S => insert (MTPrint.nameState S) (* GEN END FUNCTION EXPRESSION *)) Slist;
            menu ();
            printMenu ())
           handle MTPSplitting.Error s => abort ("MTPSplitting. Error: " ^ s)
                | MTPFilling.Error s => abort ("Filling Error: " ^ s)
                | MTPRecursion.Error s => abort ("Recursion Error: " ^ s)
                | Inference.Error s => abort ("Inference Error: " ^ s)
                | Error s => abort ("Mpi Error: " ^ s))
        end

    fun select k =
        let
          fun (* GEN BEGIN FUN FIRST *) select' (k, nil) = abort ("No such menu item") (* GEN END FUN FIRST *)
            | (* GEN BEGIN FUN BRANCH *) select' (1, Splitting O :: _) =
                let
                  (* GEN BEGIN TAG OUTSIDE LET *) val S' = (Timers.time Timers.splitting MTPSplitting.apply) O (* GEN END TAG OUTSIDE LET *)
                  (* GEN BEGIN TAG OUTSIDE LET *) val _ = pushHistory () (* GEN END TAG OUTSIDE LET *)
                  (* GEN BEGIN TAG OUTSIDE LET *) val _ = delete () (* GEN END TAG OUTSIDE LET *)
                  (* GEN BEGIN TAG OUTSIDE LET *) val _ = map ((* GEN BEGIN FUNCTION EXPRESSION *) fn S => insert (MTPrint.nameState S) (* GEN END FUNCTION EXPRESSION *)) S' (* GEN END TAG OUTSIDE LET *)
                in
                  (menu (); printMenu ())
                end (* GEN END FUN BRANCH *)
            | (* GEN BEGIN FUN BRANCH *) select' (1, Recursion O :: _) =
                let
                  (* GEN BEGIN TAG OUTSIDE LET *) val S' = (Timers.time Timers.recursion MTPRecursion.apply) O (* GEN END TAG OUTSIDE LET *)
                  (* GEN BEGIN TAG OUTSIDE LET *) val _ = pushHistory () (* GEN END TAG OUTSIDE LET *)
                  (* GEN BEGIN TAG OUTSIDE LET *) val _ = delete () (* GEN END TAG OUTSIDE LET *)
                  (* GEN BEGIN TAG OUTSIDE LET *) val _ = insert (MTPrint.nameState S') (* GEN END TAG OUTSIDE LET *)
                in
                  (menu (); printMenu ())
                end (* GEN END FUN BRANCH *)
            | (* GEN BEGIN FUN BRANCH *) select' (1, Inference O :: _) =
                let
                  (* GEN BEGIN TAG OUTSIDE LET *) val S' = (Timers.time Timers.recursion Inference.apply) O (* GEN END TAG OUTSIDE LET *)
                  (* GEN BEGIN TAG OUTSIDE LET *) val _ = pushHistory () (* GEN END TAG OUTSIDE LET *)
                  (* GEN BEGIN TAG OUTSIDE LET *) val _ = delete () (* GEN END TAG OUTSIDE LET *)
                  (* GEN BEGIN TAG OUTSIDE LET *) val _ = insert (MTPrint.nameState S') (* GEN END TAG OUTSIDE LET *)
                in
                  (menu (); printMenu ())
                end (* GEN END FUN BRANCH *)
            | (* GEN BEGIN FUN BRANCH *) select' (1, Filling O :: _) =
                let
                  (* GEN BEGIN TAG OUTSIDE LET *) val P = (Timers.time Timers.filling MTPFilling.apply) O
                    handle MTPFilling.Error _ =>  abort ("Filling unsuccessful: no object found") (* GEN END TAG OUTSIDE LET *)
                  (* GEN BEGIN TAG OUTSIDE LET *) val _ = printFillResult P (* GEN END TAG OUTSIDE LET *)
                  (* GEN BEGIN TAG OUTSIDE LET *) val _ = delete () (* GEN END TAG OUTSIDE LET *)
                  (* GEN BEGIN TAG OUTSIDE LET *) val _ = print "\n[Subgoal finished]\n" (* GEN END TAG OUTSIDE LET *)
                  (* GEN BEGIN TAG OUTSIDE LET *) val _ = print "\n" (* GEN END TAG OUTSIDE LET *)
                in
                  (menu (); printMenu ())
                end (* GEN END FUN BRANCH *)
            | (* GEN BEGIN FUN BRANCH *) select' (k, _ :: M) = select' (k-1, M) (* GEN END FUN BRANCH *)
        in
          (case !Menu of
            NONE => raise Error "No menu defined"
          | SOME M => select' (k, M))
             handle MTPSplitting.Error s => abort ("MTPSplitting. Error: " ^ s)
                  | MTPFilling.Error s => abort ("Filling Error: " ^ s)
                  | MTPRecursion.Error s => abort ("Recursion Error: " ^ s)
                  | Inference.Error s => abort ("Inference Errror: " ^ s)
                  | Error s => abort ("Mpi Error: " ^ s)
        end



    fun solve () =
        if empty () then raise Error "Nothing to prove"
        else
          let
            (* GEN BEGIN TAG OUTSIDE LET *) val S = current () (* GEN END TAG OUTSIDE LET *)
            (* GEN BEGIN TAG OUTSIDE LET *) val (Open', Solved') = MTPStrategy.run [S]
              handle MTPSplitting.Error s => abort ("MTPSplitting. Error: " ^ s)
                   | MTPFilling.Error s => abort ("Filling Error: " ^ s)
                   | MTPRecursion.Error s => abort ("Recursion Error: " ^ s)
                   | Inference.Error s => abort ("Inference Errror: " ^ s)
                   | Error s => abort ("Mpi Error: " ^ s) (* GEN END TAG OUTSIDE LET *)
            (* GEN BEGIN TAG OUTSIDE LET *) val _ = pushHistory () (* GEN END TAG OUTSIDE LET *)
            (* GEN BEGIN TAG OUTSIDE LET *) val _ = delete () (* GEN END TAG OUTSIDE LET *)
            (* GEN BEGIN TAG OUTSIDE LET *) val _ = map insertOpen Open' (* GEN END TAG OUTSIDE LET *)
            (* GEN BEGIN TAG OUTSIDE LET *) val _ = map insertSolved Solved' (* GEN END TAG OUTSIDE LET *)
          in
            (menu (); printMenu ())
          end


    fun check () =
        if empty () then raise Error "Nothing to check"
        else
          let
            (* GEN BEGIN TAG OUTSIDE LET *) val S = current () (* GEN END TAG OUTSIDE LET *)
          in
            FunTypeCheck.isState S
          end


    fun auto () =
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val (Open', Solved') = MTPStrategy.run (collectOpen ())
            handle MTPSplitting.Error s => abort ("MTPSplitting. Error: " ^ s)
                 | MTPFilling.Error s => abort ("Filling Error: " ^ s)
                 | MTPRecursion.Error s => abort ("Recursion Error: " ^ s)
                 | Inference.Error s => abort ("Inference Errror: " ^ s)
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
    (* GEN BEGIN TAG OUTSIDE LET *) val reset = reset (* GEN END TAG OUTSIDE LET *)
    (* GEN BEGIN TAG OUTSIDE LET *) val solve = solve (* GEN END TAG OUTSIDE LET *)
    (* GEN BEGIN TAG OUTSIDE LET *) val auto = auto (* GEN END TAG OUTSIDE LET *)
    (* GEN BEGIN TAG OUTSIDE LET *) val check = check (* GEN END TAG OUTSIDE LET *)
    (* GEN BEGIN TAG OUTSIDE LET *) val undo = undo (* GEN END TAG OUTSIDE LET *)
 end (* local *)
end (* GEN END FUNCTOR DECL *); (* functor MPI *)
