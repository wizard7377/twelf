(* Meta Prover Interface *)
(* Author: Carsten Schuermann *)

module Mpi (MetaGlobal : METAGLOBAL)
   (module MetaSyn' : METASYN)
   (Init : INIT)
             sharing Init.MetaSyn = MetaSyn'
             (Filling : FILLING)
             sharing Filling.MetaSyn = MetaSyn'
             (Splitting : SPLITTING)
             sharing Splitting.MetaSyn = MetaSyn'
             (Recursion : RECURSION)
             sharing Recursion.MetaSyn = MetaSyn'
             (Lemma : LEMMA)
             sharing Lemma.MetaSyn = MetaSyn'
             (Strategy : STRATEGY)
             sharing Strategy.MetaSyn = MetaSyn'
             (Qed : QED)
             sharing Qed.MetaSyn = MetaSyn'
             (MetaPrint : METAPRINT)
             sharing MetaPrint.MetaSyn = MetaSyn'
             (Names : NAMES)
             (*! sharing Names.IntSyn = MetaSyn'.IntSyn !*)
             (Timers : TIMERS)
             (Ring : RING)
  : MPI =
struct
  module MetaSyn = MetaSyn'

  exception Error of string

  local
    module M = MetaSyn
    module I = IntSyn

    type menuItem =
      Filling of Filling.operator
    | Recursion of Recursion.operator
    | Splitting of Splitting.operator

    let Open : MetaSyn.State Ring.ring ref = ref (Ring.init [])
    let Solved : MetaSyn.State Ring.ring ref = ref (Ring.init [])
    let History : (MetaSyn.State Ring.ring * MetaSyn.State Ring.ring) list ref = ref nil
    let Menu : menuItem list option ref = ref NONE

    let rec initOpen () = Open := Ring.init [];
    let rec initSolved () = Solved := Ring.init [];
    let rec empty () = Ring.empty (!Open)
    let rec current () = Ring.current (!Open)
    let rec delete () = Open := Ring.delete (!Open)
    let rec insertOpen S = Open := Ring.insert (!Open, S)
    let rec insertSolved S = Solved := Ring.insert (!Solved, S)

    let rec insert S =
        if Qed.subgoal S then
          (insertSolved S;
           print (MetaPrint.stateToString S);
           print "\n[Subgoal finished]\n";
           print "\n")
        else insertOpen S

    let rec collectOpen () = Ring.foldr op:: nil (!Open)
    let rec collectSolved () = Ring.foldr op:: nil (!Solved)
    let rec nextOpen () = Open := Ring.next (!Open)

    let rec pushHistory () =
          History :=  (!Open, !Solved) :: (!History)
    let rec popHistory () =
        case (!History)
          of nil => raise Error "History stack empty"
           | (Open', Solved') :: History' =>
             (History := History';
              Open := Open';
              Solved := Solved')


    let rec abort s =
        (print ("* " ^ s);
         raise Error s)

    let rec reset () =
        (initOpen ();
         initSolved ();
         History := nil;
         Menu := NONE)

    let rec cLToString = function (nil) -> ""
      | (c :: nil) -> 
          (I.conDecName (I.sgnLookup c))
      | (c :: L) -> 
          (I.conDecName (I.sgnLookup c)) ^ ", " ^ (cLToString L)

    let rec SplittingToMenu = function (nil, A) -> A
      | (O :: L, A) -> SplittingToMenu (L, Splitting O :: A)

    let rec FillingToMenu = function (nil, A) -> A
      | (O :: L, A) -> FillingToMenu (L, Filling O :: A)

    let rec RecursionToMenu = function (nil, A) -> A
      | (O :: L, A) -> RecursionToMenu (L, Recursion O :: A)

    let rec menu () =
        if empty () then Menu := NONE
        else
          let
            let S = current ()
            let SplitO = Splitting.expand S
            let  RecO = Recursion.expandEager S
            let (FillO, FillC) = Filling.expand S
          in
            Menu := SOME (FillingToMenu ([FillC],
                          FillingToMenu (FillO,
                                         RecursionToMenu (RecO,
                                                          SplittingToMenu (SplitO, nil)))))
          end


    let rec format k =
        if k < 10 then (Int.toString k) ^ ".  "
        else (Int.toString k) ^ ". "

    let rec menuToString () =
        let
          let rec menuToString' = function (k, nil) -> ""
            | (k, Splitting O :: M) -> 
                (menuToString' (k+1, M)) ^ "\n" ^ (format k) ^ (Splitting.menu O)
            | (k, Filling O :: M) -> 
                (menuToString' (k+1, M)) ^ "\n" ^ (format k) ^ (Filling.menu O)
            | (k, Recursion O :: M) -> 
                (menuToString' (k+1, M)) ^ "\n" ^ (format k) ^ (Recursion.menu O)
        in
          case !Menu of
            NONE => raise Error "Menu is empty"
          | SOME M => menuToString' (1, M)
        end


    let rec makeConDec (M.State (name, M.Prefix (G, M, B), V)) =
        let
          let rec makeConDec' = function (I.Null, V, k) -> I.ConDec (name, NONE, k, I.Normal, V, I.Type)
            | (I.Decl (G, D), V, k) -> 
              makeConDec' (G, I.Pi ((D, I.Maybe), V), k+1)
        in
          (makeConDec' (G, V, 0))
        end

    let rec makeSignature = function (nil) -> M.SgnEmpty
      | (S :: SL) -> 
          M.ConDec (makeConDec S,
                      makeSignature SL)
    let rec extract () =
        if empty () then makeSignature (collectSolved ())
        else (print "[Error: Proof not completed yet]\n"; M.SgnEmpty)

    let rec show () =
        print (MetaPrint.sgnToString (extract ()) ^ "\n")

    let rec printMenu () =
        if empty () then (show (); print "[QED]\n")
        else
          let
            let S = current ()
          in
            (print "\n";
             print (MetaPrint.stateToString S);
             print "\nSelect from the following menu:\n";
             print (menuToString ());
             print "\n")
          end


    let rec contains = function (nil, _) -> true
      | (x :: L, L') -> 
          (List.exists (fn x' => x = x') L') andalso contains (L, L')

    let rec equiv (L1, L2) =
          contains (L1, L2) andalso contains (L2, L1)

    let rec init' (k, cL as (c :: _)) =
        let
          let _ = MetaGlobal.maxFill := k
          let _ = reset ();
          let cL' = Order.closure c
            handle Order.Error _ => cL  (* if no termination ordering given! *)
        in
          if equiv (cL, cL') then
            map (fun S -> insert S) (Init.init cL)
          else raise Error ("Theorem by simultaneous induction not correctly stated:"
                             ^ "\n            expected: " ^ (cLToString cL'))
        end

    let rec init (k, nL) =
        let
          let rec cids = function nil -> nil
            | (name :: nL) -> 
              (case Names.stringToQid name
                 of NONE => raise Error ("Malformed qualified identifier " ^ name)
                  | SOME qid =>
              (case Names.constLookup qid
                 of NONE => raise Error ("Type family " ^ Names.qidToString qid ^ " not defined")
                  | SOME cid => cid :: (cids nL)))
        in
          ((init' (k, cids nL); menu (); printMenu ())
            handle Splitting.Error s => abort ("Splitting Error: " ^ s)
                 | Filling.Error s => abort ("Filling Error: " ^ s)
                 | Recursion.Error s => abort ("Recursion Error: " ^ s)
                 | Error s => abort ("Mpi Error: " ^ s))
        end

    let rec select k =
        let
          let rec select' = function (k, nil) -> abort ("No such menu item")
            | (1, Splitting O :: _) -> 
                let
                  let S' = (Timers.time Timers.splitting Splitting.apply) O
                  let _ = pushHistory ()
                  let _ = delete ()
                  let _ = map insert S'
                in
                  (menu (); printMenu ())
                end
            | (1, Recursion O :: _) -> 
                let
                  let S' = (Timers.time Timers.recursion Recursion.apply) O
                  let _ = pushHistory ()
                  let _ = delete ()
                  let _ = insert S'
                in
                  (menu (); printMenu ())
                end
            | (1, Filling O :: _) -> 
                let
                  let _ =
                    case (Timers.time Timers.filling Filling.apply) O of
                      nil => abort ("Filling unsuccessful: no object found")
                    | (S :: _) => (delete ();
                                   insert S;
                                   pushHistory ())
                in
                  (menu (); printMenu ())
                end
            | (k, _ :: M) -> select' (k-1, M)
        in
          (case !Menu of
            NONE => raise Error "No menu defined"
          | SOME M => select' (k, M))
             handle Splitting.Error s => abort ("Splitting Error: " ^ s)
                  | Filling.Error s => abort ("Filling Error: " ^ s)
                  | Recursion.Error s => abort ("Recursion Error: " ^ s)
                  | Error s => abort ("Mpi Error: " ^ s)
        end


    let rec lemma name =
        if empty () then raise Error "Nothing to prove"
        else
          let
            let S = current ()
            let S' = Lemma.apply (S, valOf (Names.constLookup (valOf (Names.stringToQid name))))
              handle Splitting.Error s => abort ("Splitting Error: " ^ s)
                   | Filling.Error s => abort ("Filling Error: " ^ s)
                   | Recursion.Error s => abort ("Recursion Error: " ^ s)
                   | Error s => abort ("Mpi Error: " ^ s)
            let _ = pushHistory ()
            let _ = delete ()
            let _ = insert S'
          in
            (menu (); printMenu ())
          end

    let rec solve () =
        if empty () then raise Error "Nothing to prove"
        else
          let
            let S = current ()
            let (Open', Solved') = Strategy.run [S]
              handle Splitting.Error s => abort ("Splitting Error: " ^ s)
                   | Filling.Error s => abort ("Filling Error: " ^ s)
                   | Recursion.Error s => abort ("Recursion Error: " ^ s)
                   | Error s => abort ("Mpi Error: " ^ s)
            let _ = pushHistory ()
            let _ = delete ()
            let _ = map insertOpen Open'
            let _ = map insertSolved Solved'
          in
            (menu (); printMenu ())
          end

    let rec auto () =
        let
          let (Open', Solved') = Strategy.run (collectOpen ())
            handle Splitting.Error s => abort ("Splitting Error: " ^ s)
                 | Filling.Error s => abort ("Filling Error: " ^ s)
                 | Recursion.Error s => abort ("Recursion Error: " ^ s)
                 | Error s => abort ("Mpi Error: " ^ s)
          let _ = pushHistory ()
          let _ = initOpen ()
          let _ = map insertOpen Open'
          let _ = map insertSolved Solved'
        in
          (menu (); printMenu ())
        end

    let rec next () = (nextOpen (); menu (); printMenu ())

    let rec undo () = (popHistory (); menu (); printMenu ())

  in
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
 end (* local *)
end;; (* functor MPI *)
