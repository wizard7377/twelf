(* Meta Prover Interface *)
(* Author: Carsten Schuermann *)

module MTPi (module MTPGlobal : MTPGLOBAL
              (*! module IntSyn : INTSYN !*)
              (*! module FunSyn' : FUNSYN !*)
              (*! sharing FunSyn'.IntSyn = IntSyn !*)
              module StateSyn' : STATESYN
              (*! sharing StateSyn'.IntSyn = IntSyn !*)
              (*! sharing StateSyn'.FunSyn = FunSyn' !*)
              module RelFun : RELFUN
              (*! sharing RelFun.FunSyn = FunSyn' !*)
              module Formatter : FORMATTER
              module Print : PRINT
              (*! sharing Print.IntSyn = IntSyn !*)
                sharing Print.Formatter = Formatter
              module FunTypeCheck : FUNTYPECHECK
              (*! sharing FunTypeCheck.FunSyn = FunSyn' !*)
                sharing FunTypeCheck.StateSyn = StateSyn'
              module MTPData : MTPDATA
              module MTPInit : MTPINIT
              (*! sharing MTPInit.FunSyn = FunSyn' !*)
                sharing MTPInit.StateSyn = StateSyn'
              module MTPFilling : MTPFILLING
              (*! sharing MTPFilling.FunSyn = FunSyn' !*)
                sharing MTPFilling.StateSyn = StateSyn'
              module Inference : INFERENCE
              (*! sharing Inference.FunSyn = FunSyn' !*)
                sharing Inference.StateSyn = StateSyn'
              module MTPSplitting : MTPSPLITTING
                sharing MTPSplitting.StateSyn = StateSyn'
              module MTPRecursion : MTPRECURSION
                sharing MTPRecursion.StateSyn = StateSyn'
              module MTPStrategy : MTPSTRATEGY
                sharing MTPStrategy.StateSyn = StateSyn'
              module MTPrint : MTPRINT
                sharing MTPrint.StateSyn = StateSyn'
              module Order : ORDER
              (*! sharing Order.IntSyn = IntSyn !*)
              module Names : NAMES
              (*! sharing Names.IntSyn = IntSyn !*)
              module Timers : TIMERS
              module Ring : RING)
  : MTPI =
struct
  exception Error of string

  (*! module FunSyn = FunSyn' !*)
  module StateSyn = StateSyn'

  local
    module I = IntSyn
    module F = FunSyn
    module S = StateSyn
    module Fmt = Formatter

    type MenuItem =
      Filling of MTPFilling.operator
    | Recursion of MTPRecursion.operator
    | Splitting of MTPSplitting.operator
    | Inference of Inference.operator

    let Open : StateSyn.State Ring.ring ref = ref (Ring.init [])
    let Solved : StateSyn.State Ring.ring ref = ref (Ring.init [])
    let History : (StateSyn.State Ring.ring * StateSyn.State Ring.ring) list ref = ref nil
    let Menu : MenuItem list option ref = ref NONE

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

    fun cLToString (nil) = ""
      | cLToString (c :: nil) =
          (I.conDecName (I.sgnLookup c))
      | cLToString (c :: L) =
          (I.conDecName (I.sgnLookup c)) ^ ", " ^ (cLToString L)


    fun printFillResult (_, P) =
      let
        fun formatTuple (G, P) =
          let
            fun formatTuple' (F.Unit) = nil
              | formatTuple' (F.Inx (M, F.Unit)) =
              [Print.formatExp (G, M)]
              | formatTuple' (F.Inx (M, P')) =
              (Print.formatExp (G, M) ::
               Fmt.String "," :: Fmt.Break :: formatTuple' P')
          in
            case P
              of (F.Inx (_, F.Unit)) => Fmt.Hbox (formatTuple' P)
              | _ => Fmt.HVbox0 1 1 1
                (Fmt.String "(" :: (formatTuple' P @ [Fmt.String ")"]))
          end
        let S.State (n, (G, B), (IH, OH), d, O, H, F) = current ()
      in
        TextIO.print ("Filling successful with proof term:\n" ^ (Formatter.makestring_fmt (formatTuple (G, P))) ^ "\n")
      end

    fun SplittingToMenu (nil, A) = A
      | SplittingToMenu (O :: L, A) = SplittingToMenu (L, Splitting O :: A)

    fun FillingToMenu (O, A) = Filling O :: A

    fun RecursionToMenu (O, A) = Recursion O :: A

    fun InferenceToMenu (O, A) = Inference O :: A

    fun menu () =
        if empty () then Menu := NONE
        else
          let
            let S = current ()
            let SplitO = MTPSplitting.expand S
            let InfO = Inference.expand S
            let RecO = MTPRecursion.expand S
            let FillO = MTPFilling.expand S
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
          fun menuToString' (k, nil, (NONE, _)) = (SOME k, "")
            | menuToString' (k, nil, (kopt' as SOME _, _)) = (kopt', "")
            | menuToString' (k, Splitting O :: M, kOopt' as (NONE, NONE)) =
              let
                let kOopt'' = if MTPSplitting.applicable O then (SOME k, SOME O)
                              else kOopt'
                let (kopt as SOME k'', s) = menuToString' (k+1, M, kOopt'')
              in
                (kopt, if k = k'' then s ^ "\n* " ^ (format k) ^ (MTPSplitting.menu O)
                       else s ^ "\n  " ^ (format k) ^ (MTPSplitting.menu O))
              end
            | menuToString' (k, Splitting O :: M, kOopt' as (SOME k', SOME O')) =
              let
                let kOopt'' = if MTPSplitting.applicable O then
                                case MTPSplitting.compare (O, O')
                                  of LESS => (SOME k, SOME O)
                                   | _ => kOopt'
                                else  kOopt'
                let (kopt as SOME k'', s) = menuToString' (k+1, M, kOopt'')
              in
                (kopt, if  k = k'' then s ^ "\n* " ^ (format k) ^ (MTPSplitting.menu O)
                       else s ^ "\n  " ^ (format k) ^ (MTPSplitting.menu O))
              end
            | menuToString' (k, Filling O :: M, kOopt) =
              let
                let (kopt, s) = menuToString' (k+1, M, kOopt)
              in
                (kopt, s ^ "\n  " ^ (format k) ^ (MTPFilling.menu O))
              end
            | menuToString' (k, Recursion O :: M,kOopt) =
              let
                let (kopt, s) = menuToString' (k+1, M, kOopt)
              in
                (kopt, s ^ "\n  " ^ (format k) ^ (MTPRecursion.menu O))
              end
            | menuToString' (k, Inference O :: M,kOopt) =
              let
                let (kopt, s) = menuToString' (k+1, M, kOopt)
              in
                (kopt, s ^ "\n  " ^ (format k) ^ (Inference.menu O))
              end
        in
          case !Menu of
            NONE => raise Error "Menu is empty"
          | SOME M =>
              let
                let (kopt, s) = menuToString' (1, M, (NONE, NONE))
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
            let S = current ()
            let _ = if !Global.doubleCheck then FunTypeCheck.isState S else ()
          in
            (print "\n";
             print (MTPrint.stateToString S);
             print "\nSelect from the following menu:\n";
             print (menuToString ());
             print "\n")
          end


    fun contains (nil, _) = true
      | contains (x :: L, L') =
          (List.exists (fn x' => x = x') L') andalso contains (L, L')

    fun equiv (L1, L2) =
          contains (L1, L2) andalso contains (L2, L1)

    fun transformOrder' (G, Order.Arg k) =
        let
          let k' = (I.ctxLength G) -k+1
          let I.Dec (_, V) = I.ctxDec (G, k')
        in
          S.Arg ((I.Root (I.BVar k', I.Nil), I.id), (V, I.id))
        end
      | transformOrder' (G, Order.Lex Os) =
          S.Lex (map (fun O -> transformOrder' (G, O)) Os)
      | transformOrder' (G, Order.Simul Os) =
          S.Simul (map (fun O -> transformOrder' (G, O)) Os)

    fun transformOrder (G, F.All (F.Prim D, F), Os) =
          S.All (D, transformOrder (I.Decl (G, D), F, Os))
      | transformOrder (G, F.And (F1, F2), O :: Os) =
          S.And (transformOrder (G, F1, [O]),
                 transformOrder (G, F2, Os))
      | transformOrder (G, F.Ex _, [O]) = transformOrder' (G, O)

    fun select c = (Order.selLookup c handle _ => Order.Lex [])

    fun init (k, names) =
        let
          let cL = map (fun x -> valOf (Names.constLookup (valOf (Names.stringToQid x)))) names
          let _ = MTPGlobal.maxFill := k
          let _ = reset ();
          let F = RelFun.convertFor cL
          let O = transformOrder (I.Null, F, map select cL)
          let Slist = MTPInit.init (F, O)
          let _ = if List.length Slist =0 then raise Domain else ()
        in
          ((map (fun S -> insert (MTPrint.nameState S)) Slist;
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
          fun select' (k, nil) = abort ("No such menu item")
            | select' (1, Splitting O :: _) =
                let
                  let S' = (Timers.time Timers.splitting MTPSplitting.apply) O
                  let _ = pushHistory ()
                  let _ = delete ()
                  let _ = map (fun S -> insert (MTPrint.nameState S)) S'
                in
                  (menu (); printMenu ())
                end
            | select' (1, Recursion O :: _) =
                let
                  let S' = (Timers.time Timers.recursion MTPRecursion.apply) O
                  let _ = pushHistory ()
                  let _ = delete ()
                  let _ = insert (MTPrint.nameState S')
                in
                  (menu (); printMenu ())
                end
            | select' (1, Inference O :: _) =
                let
                  let S' = (Timers.time Timers.recursion Inference.apply) O
                  let _ = pushHistory ()
                  let _ = delete ()
                  let _ = insert (MTPrint.nameState S')
                in
                  (menu (); printMenu ())
                end
            | select' (1, Filling O :: _) =
                let
                  let P = (Timers.time Timers.filling MTPFilling.apply) O
                    handle MTPFilling.Error _ =>  abort ("Filling unsuccessful: no object found")
                  let _ = printFillResult P
                  let _ = delete ()
                  let _ = print "\n[Subgoal finished]\n"
                  let _ = print "\n"
                in
                  (menu (); printMenu ())
                end
            | select' (k, _ :: M) = select' (k-1, M)
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
            let S = current ()
            let (Open', Solved') = MTPStrategy.run [S]
              handle MTPSplitting.Error s => abort ("MTPSplitting. Error: " ^ s)
                   | MTPFilling.Error s => abort ("Filling Error: " ^ s)
                   | MTPRecursion.Error s => abort ("Recursion Error: " ^ s)
                   | Inference.Error s => abort ("Inference Errror: " ^ s)
                   | Error s => abort ("Mpi Error: " ^ s)
            let _ = pushHistory ()
            let _ = delete ()
            let _ = map insertOpen Open'
            let _ = map insertSolved Solved'
          in
            (menu (); printMenu ())
          end


    fun check () =
        if empty () then raise Error "Nothing to check"
        else
          let
            let S = current ()
          in
            FunTypeCheck.isState S
          end


    fun auto () =
        let
          let (Open', Solved') = MTPStrategy.run (collectOpen ())
            handle MTPSplitting.Error s => abort ("MTPSplitting. Error: " ^ s)
                 | MTPFilling.Error s => abort ("Filling Error: " ^ s)
                 | MTPRecursion.Error s => abort ("Recursion Error: " ^ s)
                 | Inference.Error s => abort ("Inference Errror: " ^ s)
                 | Error s => abort ("Mpi Error: " ^ s)
          let _ = pushHistory ()
          let _ = initOpen ()
          let _ = map insertOpen Open'
          let _ = map insertSolved Solved'
        in
          (menu (); printMenu ())
        end


    fun next () = (nextOpen (); menu (); printMenu ())

    fun undo () = (popHistory (); menu (); printMenu ())

  in
    let init = init
    let select = select
    let print = printMenu
    let next = next
    let reset = reset
    let solve = solve
    let auto = auto
    let check = check
    let undo = undo
 end (* local *)
end;; (* functor MPI *)
