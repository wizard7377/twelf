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

    type MenuItem =
      Filling of Filling.operator
    | Recursion of Recursion.operator
    | Splitting of Splitting.operator

    let Open : MetaSyn.State Ring.ring ref = ref (Ring.init [])
    let Solved : MetaSyn.State Ring.ring ref = ref (Ring.init [])
    let History : (MetaSyn.State Ring.ring * MetaSyn.State Ring.ring) list ref = ref nil
    let Menu : MenuItem list option ref = ref NONE

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

    fun cLToString (nil) = ""
      | cLToString (c :: nil) =
          (I.conDecName (I.sgnLookup c))
      | cLToString (c :: L) =
          (I.conDecName (I.sgnLookup c)) ^ ", " ^ (cLToString L)

    fun SplittingToMenu (nil, A) = A
      | SplittingToMenu (O :: L, A) = SplittingToMenu (L, Splitting O :: A)

    fun FillingToMenu (nil, A) = A
      | FillingToMenu (O :: L, A) = FillingToMenu (L, Filling O :: A)

    fun RecursionToMenu (nil, A) = A
      | RecursionToMenu (O :: L, A) = RecursionToMenu (L, Recursion O :: A)

    fun menu () =
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


    fun format k =
        if k < 10 then (Int.toString k) ^ ".  "
        else (Int.toString k) ^ ". "

    fun menuToString () =
        let
          fun menuToString' (k, nil) = ""
            | menuToString' (k, Splitting O :: M) =
                (menuToString' (k+1, M)) ^ "\n" ^ (format k) ^ (Splitting.menu O)
            | menuToString' (k, Filling O :: M) =
                (menuToString' (k+1, M)) ^ "\n" ^ (format k) ^ (Filling.menu O)
            | menuToString' (k, Recursion O :: M) =
                (menuToString' (k+1, M)) ^ "\n" ^ (format k) ^ (Recursion.menu O)
        in
          case !Menu of
            NONE => raise Error "Menu is empty"
          | SOME M => menuToString' (1, M)
        end


    fun makeConDec (M.State (name, M.Prefix (G, M, B), V)) =
        let
          fun makeConDec' (I.Null, V, k) = I.ConDec (name, NONE, k, I.Normal, V, I.Type)
            | makeConDec' (I.Decl (G, D), V, k) =
              makeConDec' (G, I.Pi ((D, I.Maybe), V), k+1)
        in
          (makeConDec' (G, V, 0))
        end

    fun makeSignature (nil) = M.SgnEmpty
      | makeSignature (S :: SL) =
          M.ConDec (makeConDec S,
                      makeSignature SL)
    fun extract () =
        if empty () then makeSignature (collectSolved ())
        else (print "[Error: Proof not completed yet]\n"; M.SgnEmpty)

    fun show () =
        print (MetaPrint.sgnToString (extract ()) ^ "\n")

    fun printMenu () =
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


    fun contains (nil, _) = true
      | contains (x :: L, L') =
          (List.exists (fn x' => x = x') L') andalso contains (L, L')

    fun equiv (L1, L2) =
          contains (L1, L2) andalso contains (L2, L1)

    fun init' (k, cL as (c :: _)) =
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

    fun init (k, nL) =
        let
          fun cids nil = nil
            | cids (name :: nL) =
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

    fun select k =
        let
          fun select' (k, nil) = abort ("No such menu item")
            | select' (1, Splitting O :: _) =
                let
                  let S' = (Timers.time Timers.splitting Splitting.apply) O
                  let _ = pushHistory ()
                  let _ = delete ()
                  let _ = map insert S'
                in
                  (menu (); printMenu ())
                end
            | select' (1, Recursion O :: _) =
                let
                  let S' = (Timers.time Timers.recursion Recursion.apply) O
                  let _ = pushHistory ()
                  let _ = delete ()
                  let _ = insert S'
                in
                  (menu (); printMenu ())
                end
            | select' (1, Filling O :: _) =
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
            | select' (k, _ :: M) = select' (k-1, M)
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

    fun solve () =
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

    fun auto () =
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

    fun next () = (nextOpen (); menu (); printMenu ())

    fun undo () = (popHistory (); menu (); printMenu ())

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
