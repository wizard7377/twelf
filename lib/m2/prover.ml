(* Meta Prover *)

(* Author: Carsten Schuermann *)

module type PROVER = sig
  (*! structure IntSyn : Intsyn.INTSYN !*)
  exception Error of string

  val init : int * IntSyn.cid list -> unit
  val auto : unit -> unit
  val print : unit -> unit
  val install : (IntSyn.conDec -> IntSyn.cid) -> unit
end

(* signature PROVER *)
(* Meta Prover *)

(* Author: Carsten Schuermann *)

module Prover
    (MetaGlobal : Meta_global.METAGLOBAL)
    (MetaSyn' : Metasyn.METASYN)
    (Init : Init.INIT)
    (Strategy : Strategy.STRATEGY)
    (Filling : Filling.Fill.FILLING)
    (Splitting : Splitting.Split.SPLITTING)
    (Recursion : Recursion.RECURSION)
    (Qed : Qed.QED)
    (MetaPrint : Meta_print.METAPRINT)
    (Names : Names.NAMES)
    (Timers : Timers.TIMERS) : PROVER = struct
  (*! structure IntSyn = MetaSyn'.IntSyn !*)

  exception Error of string

  module MetaSyn = MetaSyn'
  module M = MetaSyn
  module I = IntSyn
  (* List of open states *)

  let openStates : MetaSyn.state list ref = ref []
  (* List of solved states *)

  let solvedStates : MetaSyn.state list ref = ref []
  let rec error s = raise (Error s)
  (* reset () = ()

       Invariant:
       Resets the internal state of open states/solved states
    *)

  let rec reset () =
    openStates := [];
    solvedStates := []
  (* contains (L1, L2) = B'

       Invariant:
       B' holds iff L1 subset of L2 (modulo permutation)
    *)

  let rec contains = function
    | [], _ -> true
    | x :: L, L' -> List.exists (fun x' -> x = x') L' && contains (L, L')
  (* equiv (L1, L2) = B'

       Invariant:
       B' holds iff L1 is equivalent to L2 (modulo permutation)
    *)

  let rec equiv (L1, L2) = contains (L1, L2) && contains (L2, L1)
  (* insertState S = ()

       Invariant:
       If S is successful prove state, S is stored in solvedStates
       else S is stored in openStates
    *)

  let rec insertState S =
    if Qed.subgoal S then solvedStates := S :: !solvedStates
    else openStates := S :: !openStates
  (* cLtoString L = s

       Invariant:
       If   L is a list of cid,
       then s is a string, listing their names
    *)

  let rec cLToString = function
    | [] -> ""
    | c :: [] -> I.conDecName (I.sgnLookup c)
    | c :: L -> I.conDecName (I.sgnLookup c) ^ ", " ^ cLToString L
  (* init (k, cL) = ()

       Invariant:
       If   k is the maximal search depth
       and  cL is a complete and consistent list of cids
       then init initializes the openStates/solvedStates
       else an Error exception is raised
    *)

  let rec init (k, cL) =
    (* if no termination ordering given! *)
    let _ = MetaGlobal.maxFill := k in
    let _ = reset () in
    let cL' = try Order.closure c with Order.Error _ -> cL in
    if equiv (cL, cL') then List.app (fun S -> insertState S) (Init.init cL)
    else
      raise
        (Error
           ("Theorem by simultaneous induction not correctly stated:"
          ^ "\n            expected: " ^ cLToString cL'))
  (* auto () = ()

       Invariant:
       many States in possible.
    *)

  let rec auto () =
    let _ = print "M2.Prover.auto\n" in
    let Open, solvedStates' =
      try Strategy.run !openStates with
      | Splitting.Error s -> error ("Splitting Error: " ^ s)
      | Filling.Error s ->
          error ("A proof could not be found -- Filling Error: " ^ s)
      | Recursion.Error s -> error ("Recursion Error: " ^ s)
      | Filling.TimeOut ->
          error "A proof could not be found -- Exceeding Time Limit\n"
    in
    let _ = openStates := Open in
    let _ = solvedStates := !solvedStates @ solvedStates' in
    if List.length !openStates > 0 then
      raise (Error "A proof could not be found")
    else ()
  (* makeConDec (name, (G, M), V) = e'

       Invariant:
       If   |- G ctx
       and  G |- M mtx
       and  G |- V : type
       then e' = (name, |G|, {G}.V, Type) is a signature conDec
    *)

  let rec makeConDec (M.State (name, M.Prefix (G, M, B), V)) =
    let rec makeConDec' = function
      | I.Null, V, k -> I.ConDec (name, None, k, I.Normal, V, I.Type)
      | I.Decl (G, D), V, k -> makeConDec' (G, I.Pi ((D, I.Maybe), V), k + 1)
    in
    makeConDec' (G, V, 0)
  (* makeSignature (SL) = IS'

       Invariant:
       If   SL is a list of states,
       then IS' is the corresponding interface signaure
    *)

  let rec makeSignature = function
    | [] -> M.SgnEmpty
    | S :: SL -> M.ConDec (makeConDec S, makeSignature SL)
  (* install () = ()

       Invariant:
       Installs solved states into the global signature.
    *)

  let rec install installConDec =
    let rec install' = function
      | M.SgnEmpty -> ()
      | M.ConDec (e, S) ->
          installConDec e;
          install' S
    in
    let IS =
      if List.length !openStates > 0 then raise (Error "Theorem not proven")
      else makeSignature !solvedStates
    in
    install' IS;
    if !Global.chatter > 2 then (
      print "% ------------------\n";
      print (MetaPrint.sgnToString IS);
      print "% ------------------\n")
    else ()
  (* print () = ()

       Invariant:
       Prints the list of open States and the list of closed states.
    *)

  let rec printState () =
    let rec print' = function
      | [] -> ()
      | S :: L ->
          print (MetaPrint.stateToString S);
          print' L
    in
    print "Open problems:\n";
    print "==============\n\n";
    print' !openStates;
    print "Solved problems:\n";
    print "================\n\n";
    print' !solvedStates

  let print = printState
  let init = init
  let auto = auto
  let install = install
  (* local *)
end

(* functor Prover *)
