(* Meta Prover Interface *)


(* Author: Carsten Schuermann *)


module MTPi (MTPGlobal : MTPGLOBAL) (StateSyn' : STATESYN) (RelFun : RELFUN) (Formatter : FORMATTER) (Print : PRINT) (FunTypeCheck : FUNTYPECHECK) (MTPData : MTPDATA) (MTPInit : MTPINIT) (MTPFilling : MTPFILLING) (Inference : INFERENCE) (MTPSplitting : MTPSPLITTING) (MTPRecursion : MTPRECURSION) (MTPStrategy : MTPSTRATEGY) (MTPrint : MTPRINT) (Order : ORDER) (Names : NAMES) (Timers : TIMERS) (Ring : RING) : MTPI = struct exception Error of string
(*! structure FunSyn = FunSyn' !*)

module StateSyn = StateSyn'
module I = IntSyn
module F = FunSyn
module S = StateSyn
module Fmt = Formatter
type menuItem = Filling of MTPFilling.operator | Recursion of MTPRecursion.operator | Splitting of MTPSplitting.operator | Inference of Inference.operator
let Open : StateSyn.state Ring.ring ref = ref (Ring.init [])
let Solved : StateSyn.state Ring.ring ref = ref (Ring.init [])
let History : StateSyn.state Ring.ring * StateSyn.state Ring.ring list ref = ref []
let Menu : menuItem list option ref = ref None
let rec initOpen ()  = Open := Ring.init []
let rec initSolved ()  = Solved := Ring.init []
let rec empty ()  = Ring.empty (! Open)
let rec current ()  = Ring.current (! Open)
let rec delete ()  = Open := Ring.delete (! Open)
let rec insertOpen S  = Open := Ring.insert (! Open, S)
let rec insertSolved S  = Solved := Ring.insert (! Solved, S)
let rec insert S  = insertOpen S
let rec collectOpen ()  = Ring.foldr :: [] (! Open)
let rec collectSolved ()  = Ring.foldr :: [] (! Solved)
let rec nextOpen ()  = Open := Ring.next (! Open)
let rec pushHistory ()  = History := (! Open, ! Solved) :: (! History)
let rec popHistory ()  = match (! History) with [] -> raise (Error "History stack empty") | (Open', Solved') :: History' -> (History := History'; Open := Open'; Solved := Solved')
let rec abort s  = (print ("* " ^ s); raise (Error s))
let rec reset ()  = (initOpen (); initSolved (); History := []; Menu := None)
let rec cLToString = function ([]) -> "" | (c :: []) -> (I.conDecName (I.sgnLookup c)) | (c :: L) -> (I.conDecName (I.sgnLookup c)) ^ ", " ^ (cLToString L)
let rec printFillResult (_, P)  = ( let rec formatTuple (G, P)  = ( let rec formatTuple' = function (F.Unit) -> [] | (F.Inx (M, F.Unit)) -> [Print.formatExp (G, M)] | (F.Inx (M, P')) -> (Print.formatExp (G, M) :: Fmt.String "," :: Fmt.Break :: formatTuple' P') in  match P with (F.Inx (_, F.Unit)) -> Fmt.Hbox (formatTuple' P) | _ -> Fmt.HVbox0 1 1 1 (Fmt.String "(" :: (formatTuple' P @ [Fmt.String ")"])) ) in let S.State (n, (G, B), (IH, OH), d, O, H, F) = current () in  TextIO.print ("Filling successful with proof term:\n" ^ (Formatter.makestring_fmt (formatTuple (G, P))) ^ "\n") )
let rec SplittingToMenu = function ([], A) -> A | (O :: L, A) -> SplittingToMenu (L, Splitting O :: A)
let rec FillingToMenu (O, A)  = Filling O :: A
let rec RecursionToMenu (O, A)  = Recursion O :: A
let rec InferenceToMenu (O, A)  = Inference O :: A
let rec menu ()  = if empty () then Menu := None else ( let S = current () in let SplitO = MTPSplitting.expand S in let InfO = Inference.expand S in let RecO = MTPRecursion.expand S in let FillO = MTPFilling.expand S in  Menu := Some (FillingToMenu (FillO, RecursionToMenu (RecO, InferenceToMenu (InfO, SplittingToMenu (SplitO, []))))) )
let rec format k  = if k < 10 then (Int.toString k) ^ ".  " else (Int.toString k) ^ ". "
let rec menuToString ()  = ( let rec menuToString' = function (k, [], (None, _)) -> (Some k, "") | (k, [], (kopt', _)) -> (kopt', "") | (k, Splitting O :: M, kOopt') -> ( let kOopt'' = if MTPSplitting.applicable O then (Some k, Some O) else kOopt' in let (kopt, s) = menuToString' (k + 1, M, kOopt'') in  (kopt, if k = k'' then s ^ "\n* " ^ (format k) ^ (MTPSplitting.menu O) else s ^ "\n  " ^ (format k) ^ (MTPSplitting.menu O)) ) | (k, Splitting O :: M, kOopt') -> ( let kOopt'' = if MTPSplitting.applicable O then match MTPSplitting.compare (O, O') with Lt -> (Some k, Some O) | _ -> kOopt' else kOopt' in let (kopt, s) = menuToString' (k + 1, M, kOopt'') in  (kopt, if k = k'' then s ^ "\n* " ^ (format k) ^ (MTPSplitting.menu O) else s ^ "\n  " ^ (format k) ^ (MTPSplitting.menu O)) ) | (k, Filling O :: M, kOopt) -> ( let (kopt, s) = menuToString' (k + 1, M, kOopt) in  (kopt, s ^ "\n  " ^ (format k) ^ (MTPFilling.menu O)) ) | (k, Recursion O :: M, kOopt) -> ( let (kopt, s) = menuToString' (k + 1, M, kOopt) in  (kopt, s ^ "\n  " ^ (format k) ^ (MTPRecursion.menu O)) ) | (k, Inference O :: M, kOopt) -> ( let (kopt, s) = menuToString' (k + 1, M, kOopt) in  (kopt, s ^ "\n  " ^ (format k) ^ (Inference.menu O)) ) in  match ! Menu with None -> raise (Error "Menu is empty") | Some M -> ( let (kopt, s) = menuToString' (1, M, (None, None)) in  s ) )
let rec printMenu ()  = if empty () then (print "[QED]\n"; print ("Statistics: required Twelf.Prover.maxFill := " ^ (Int.toString (! MTPData.maxFill)) ^ "\n")) else ( let S = current () in let _ = if ! Global.doubleCheck then FunTypeCheck.isState S else () in  (print "\n"; print (MTPrint.stateToString S); print "\nSelect from the following menu:\n"; print (menuToString ()); print "\n") )
let rec contains = function ([], _) -> true | (x :: L, L') -> (List.exists (fun x' -> x = x') L') && contains (L, L')
let rec equiv (L1, L2)  = contains (L1, L2) && contains (L2, L1)
let rec transformOrder' = function (G, Order.Arg k) -> ( let k' = (I.ctxLength G) - k + 1 in let I.Dec (_, V) = I.ctxDec (G, k') in  S.Arg ((I.Root (I.BVar k', I.Nil), I.id), (V, I.id)) ) | (G, Order.Lex Os) -> S.Lex (map (fun O -> transformOrder' (G, O)) Os) | (G, Order.Simul Os) -> S.Simul (map (fun O -> transformOrder' (G, O)) Os)
let rec transformOrder = function (G, F.All (F.Prim D, F), Os) -> S.All (D, transformOrder (I.Decl (G, D), F, Os)) | (G, F.And (F1, F2), O :: Os) -> S.And (transformOrder (G, F1, [O]), transformOrder (G, F2, Os)) | (G, F.Ex _, [O]) -> transformOrder' (G, O)
let rec select c  = (try Order.selLookup c with _ -> Order.Lex [])
let rec init (k, names)  = ( let cL = map (fun x -> valOf (Names.constLookup (valOf (Names.stringToQid x)))) names in let _ = MTPGlobal.maxFill := k in let _ = reset () in let F = RelFun.convertFor cL in let O = transformOrder (I.Null, F, map select cL) in let Slist = MTPInit.init (F, O) in let _ = if List.length Slist = 0 then raise (Domain) else () in  (try (map (fun S -> insert (MTPrint.nameState S)) Slist; menu (); printMenu ()) with MTPSplitting.Error s -> abort ("MTPSplitting. Error: " ^ s) | MTPFilling.Error s -> abort ("Filling Error: " ^ s) | MTPRecursion.Error s -> abort ("Recursion Error: " ^ s) | Inference.Error s -> abort ("Inference Error: " ^ s) | Error s -> abort ("Mpi Error: " ^ s)) )
let rec select k  = ( let rec select' = function (k, []) -> abort ("No such menu item") | (1, Splitting O :: _) -> ( let S' = (Timers.time Timers.splitting MTPSplitting.apply) O in let _ = pushHistory () in let _ = delete () in let _ = map (fun S -> insert (MTPrint.nameState S)) S' in  (menu (); printMenu ()) ) | (1, Recursion O :: _) -> ( let S' = (Timers.time Timers.recursion MTPRecursion.apply) O in let _ = pushHistory () in let _ = delete () in let _ = insert (MTPrint.nameState S') in  (menu (); printMenu ()) ) | (1, Inference O :: _) -> ( let S' = (Timers.time Timers.recursion Inference.apply) O in let _ = pushHistory () in let _ = delete () in let _ = insert (MTPrint.nameState S') in  (menu (); printMenu ()) ) | (1, Filling O :: _) -> ( let P = try (Timers.time Timers.filling MTPFilling.apply) O with MTPFilling.Error _ -> abort ("Filling unsuccessful: no object found") in let _ = printFillResult P in let _ = delete () in let _ = print "\n[Subgoal finished]\n" in let _ = print "\n" in  (menu (); printMenu ()) ) | (k, _ :: M) -> select' (k - 1, M) in  try (match ! Menu with None -> raise (Error "No menu defined") | Some M -> select' (k, M)) with MTPSplitting.Error s -> abort ("MTPSplitting. Error: " ^ s) | MTPFilling.Error s -> abort ("Filling Error: " ^ s) | MTPRecursion.Error s -> abort ("Recursion Error: " ^ s) | Inference.Error s -> abort ("Inference Errror: " ^ s) | Error s -> abort ("Mpi Error: " ^ s) )
let rec solve ()  = if empty () then raise (Error "Nothing to prove") else ( let S = current () in let (Open', Solved') = try MTPStrategy.run [S] with MTPSplitting.Error s -> abort ("MTPSplitting. Error: " ^ s) | MTPFilling.Error s -> abort ("Filling Error: " ^ s) | MTPRecursion.Error s -> abort ("Recursion Error: " ^ s) | Inference.Error s -> abort ("Inference Errror: " ^ s) | Error s -> abort ("Mpi Error: " ^ s) in let _ = pushHistory () in let _ = delete () in let _ = map insertOpen Open' in let _ = map insertSolved Solved' in  (menu (); printMenu ()) )
let rec check ()  = if empty () then raise (Error "Nothing to check") else ( let S = current () in  FunTypeCheck.isState S )
let rec auto ()  = ( let (Open', Solved') = try MTPStrategy.run (collectOpen ()) with MTPSplitting.Error s -> abort ("MTPSplitting. Error: " ^ s) | MTPFilling.Error s -> abort ("Filling Error: " ^ s) | MTPRecursion.Error s -> abort ("Recursion Error: " ^ s) | Inference.Error s -> abort ("Inference Errror: " ^ s) | Error s -> abort ("Mpi Error: " ^ s) in let _ = pushHistory () in let _ = initOpen () in let _ = map insertOpen Open' in let _ = map insertSolved Solved' in  (menu (); printMenu ()) )
let rec next ()  = (nextOpen (); menu (); printMenu ())
let rec undo ()  = (popHistory (); menu (); printMenu ())
let init = init
let select = select
let print = printMenu
let next = next
let reset = reset
let solve = solve
let auto = auto
let check = check
let undo = undo
(* local *)

 end


(* functor MPI *)

