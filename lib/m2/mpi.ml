(* Meta Prover Interface *)

(* Author: Carsten Schuermann *)

module Mpi
    (MetaGlobal : METAGLOBAL)
    (MetaSyn' : METASYN)
    (Init : INIT)
    (Filling : FILLING)
    (Splitting : SPLITTING)
    (Recursion : RECURSION)
    (Lemma : LEMMA)
    (Strategy : STRATEGY)
    (Qed : QED)
    (MetaPrint : METAPRINT)
    (Names : NAMES)
    (Timers : TIMERS)
    (Ring : RING) : MPI = struct
  module MetaSyn = MetaSyn'

  exception Error of string

  module M = MetaSyn
  module I = IntSyn

  type menuItem =
    | Filling of Filling.operator
    | Recursion of Recursion.operator
    | Splitting of Splitting.operator

  let Open : MetaSyn.state Ring.ring ref = ref (Ring.init [])
  let Solved : MetaSyn.state Ring.ring ref = ref (Ring.init [])

  let History : MetaSyn.state Ring.ring * MetaSyn.state Ring.ring list ref =
    ref []

  let Menu : menuItem list option ref = ref None
  let rec initOpen () = Open := Ring.init []
  let rec initSolved () = Solved := Ring.init []
  let rec empty () = Ring.empty !Open
  let rec current () = Ring.current !Open
  let rec delete () = Open := Ring.delete !Open
  let rec insertOpen S = Open := Ring.insert (!Open, S)
  let rec insertSolved S = Solved := Ring.insert (!Solved, S)

  let rec insert S =
    if Qed.subgoal S then (
      insertSolved S;
      print (MetaPrint.stateToString S);
      print "\n[Subgoal finished]\n";
      print "\n")
    else insertOpen S

  let rec collectOpen () = Ring.foldr :: [] !Open
  let rec collectSolved () = Ring.foldr :: [] !Solved
  let rec nextOpen () = Open := Ring.next !Open
  let rec pushHistory () = History := (!Open, !Solved) :: !History

  let rec popHistory () =
    match !History with
    | [] -> raise (Error "History stack empty")
    | (Open', Solved') :: History' ->
        History := History';
        Open := Open';
        Solved := Solved'

  let rec abort s =
    print ("* " ^ s);
    raise (Error s)

  let rec reset () =
    initOpen ();
    initSolved ();
    History := [];
    Menu := None

  let rec cLToString = function
    | [] -> ""
    | c :: [] -> I.conDecName (I.sgnLookup c)
    | c :: L -> I.conDecName (I.sgnLookup c) ^ ", " ^ cLToString L

  let rec SplittingToMenu = function
    | [], A -> A
    | O :: L, A -> SplittingToMenu (L, Splitting O :: A)

  let rec FillingToMenu = function
    | [], A -> A
    | O :: L, A -> FillingToMenu (L, Filling O :: A)

  let rec RecursionToMenu = function
    | [], A -> A
    | O :: L, A -> RecursionToMenu (L, Recursion O :: A)

  let rec menu () =
    if empty () then Menu := None
    else
      let S = current () in
      let SplitO = Splitting.expand S in
      let RecO = Recursion.expandEager S in
      let FillO, FillC = Filling.expand S in
      Menu :=
        Some
          (FillingToMenu
             ( [ FillC ],
               FillingToMenu
                 (FillO, RecursionToMenu (RecO, SplittingToMenu (SplitO, [])))
             ))

  let rec format k =
    if k < 10 then Int.toString k ^ ".  " else Int.toString k ^ ". "

  let rec menuToString () =
    let rec menuToString' = function
      | k, [] -> ""
      | k, Splitting O :: M ->
          menuToString' (k + 1, M) ^ "\n" ^ format k ^ Splitting.menu O
      | k, Filling O :: M ->
          menuToString' (k + 1, M) ^ "\n" ^ format k ^ Filling.menu O
      | k, Recursion O :: M ->
          menuToString' (k + 1, M) ^ "\n" ^ format k ^ Recursion.menu O
    in
    match !Menu with
    | None -> raise (Error "Menu is empty")
    | Some M -> menuToString' (1, M)

  let rec makeConDec (M.State (name, M.Prefix (G, M, B), V)) =
    let rec makeConDec' = function
      | I.Null, V, k -> I.ConDec (name, None, k, I.Normal, V, I.Type)
      | I.Decl (G, D), V, k -> makeConDec' (G, I.Pi ((D, I.Maybe), V), k + 1)
    in
    makeConDec' (G, V, 0)

  let rec makeSignature = function
    | [] -> M.SgnEmpty
    | S :: SL -> M.ConDec (makeConDec S, makeSignature SL)

  let rec extract () =
    if empty () then makeSignature (collectSolved ())
    else (
      print "[Error: Proof not completed yet]\n";
      M.SgnEmpty)

  let rec show () = print (MetaPrint.sgnToString (extract ()) ^ "\n")

  let rec printMenu () =
    if empty () then (
      show ();
      print "[QED]\n")
    else
      let S = current () in
      print "\n";
      print (MetaPrint.stateToString S);
      print "\nSelect from the following menu:\n";
      print (menuToString ());
      print "\n"

  let rec contains = function
    | [], _ -> true
    | x :: L, L' -> List.exists (fun x' -> x = x') L' && contains (L, L')

  let rec equiv (L1, L2) = contains (L1, L2) && contains (L2, L1)

  let rec init' (k, cL) =
    (* if no termination ordering given! *)
    let _ = MetaGlobal.maxFill := k in
    let _ = reset () in
    let cL' = try Order.closure c with Order.Error _ -> cL in
    if equiv (cL, cL') then map (fun S -> insert S) (Init.init cL)
    else
      raise
        (Error
           ("Theorem by simultaneous induction not correctly stated:"
          ^ "\n            expected: " ^ cLToString cL'))

  let rec init (k, nL) =
    let rec cids = function
      | [] -> []
      | name :: nL -> (
          match Names.stringToQid name with
          | None -> raise (Error ("Malformed qualified identifier " ^ name))
          | Some qid -> (
              match Names.constLookup qid with
              | None ->
                  raise
                    (Error
                       ("Type family " ^ Names.qidToString qid ^ " not defined"))
              | Some cid -> cid :: cids nL))
    in
    try
      init' (k, cids nL);
      menu ();
      printMenu ()
    with
    | Splitting.Error s -> abort ("Splitting Error: " ^ s)
    | Filling.Error s -> abort ("Filling Error: " ^ s)
    | Recursion.Error s -> abort ("Recursion Error: " ^ s)
    | Error s -> abort ("Mpi Error: " ^ s)

  let rec select k =
    let rec select' = function
      | k, [] -> abort "No such menu item"
      | 1, Splitting O :: _ ->
          let S' = (Timers.time Timers.splitting Splitting.apply) O in
          let _ = pushHistory () in
          let _ = delete () in
          let _ = map insert S' in
          menu ();
          printMenu ()
      | 1, Recursion O :: _ ->
          let S' = (Timers.time Timers.recursion Recursion.apply) O in
          let _ = pushHistory () in
          let _ = delete () in
          let _ = insert S' in
          menu ();
          printMenu ()
      | 1, Filling O :: _ ->
          let _ =
            match (Timers.time Timers.filling Filling.apply) O with
            | [] -> abort "Filling unsuccessful: no object found"
            | S :: _ ->
                delete ();
                insert S;
                pushHistory ()
          in
          menu ();
          printMenu ()
      | k, _ :: M -> select' (k - 1, M)
    in
    try
      match !Menu with
      | None -> raise (Error "No menu defined")
      | Some M -> select' (k, M)
    with
    | Splitting.Error s -> abort ("Splitting Error: " ^ s)
    | Filling.Error s -> abort ("Filling Error: " ^ s)
    | Recursion.Error s -> abort ("Recursion Error: " ^ s)
    | Error s -> abort ("Mpi Error: " ^ s)

  let rec lemma name =
    if empty () then raise (Error "Nothing to prove")
    else
      let S = current () in
      let S' =
        try
          Lemma.apply
            (S, valOf (Names.constLookup (valOf (Names.stringToQid name))))
        with
        | Splitting.Error s -> abort ("Splitting Error: " ^ s)
        | Filling.Error s -> abort ("Filling Error: " ^ s)
        | Recursion.Error s -> abort ("Recursion Error: " ^ s)
        | Error s -> abort ("Mpi Error: " ^ s)
      in
      let _ = pushHistory () in
      let _ = delete () in
      let _ = insert S' in
      menu ();
      printMenu ()

  let rec solve () =
    if empty () then raise (Error "Nothing to prove")
    else
      let S = current () in
      let Open', Solved' =
        try Strategy.run [ S ] with
        | Splitting.Error s -> abort ("Splitting Error: " ^ s)
        | Filling.Error s -> abort ("Filling Error: " ^ s)
        | Recursion.Error s -> abort ("Recursion Error: " ^ s)
        | Error s -> abort ("Mpi Error: " ^ s)
      in
      let _ = pushHistory () in
      let _ = delete () in
      let _ = map insertOpen Open' in
      let _ = map insertSolved Solved' in
      menu ();
      printMenu ()

  let rec auto () =
    let Open', Solved' =
      try Strategy.run (collectOpen ()) with
      | Splitting.Error s -> abort ("Splitting Error: " ^ s)
      | Filling.Error s -> abort ("Filling Error: " ^ s)
      | Recursion.Error s -> abort ("Recursion Error: " ^ s)
      | Error s -> abort ("Mpi Error: " ^ s)
    in
    let _ = pushHistory () in
    let _ = initOpen () in
    let _ = map insertOpen Open' in
    let _ = map insertSolved Solved' in
    menu ();
    printMenu ()

  let rec next () =
    nextOpen ();
    menu ();
    printMenu ()

  let rec undo () =
    popHistory ();
    menu ();
    printMenu ()

  let init = init
  let select = select
  let print = printMenu
  let next = next
  let lemma = lemma
  let reset = reset
  let solve = solve
  let auto = auto
  let extract = extract
  let show = show
  let undo = undo
  (* local *)
end

(* functor MPI *)
