open Basis

(* Meta Prover Version 1.3 *)

(* Author: Carsten Schuermann *)

module type MTPROVER = sig
  (*! structure FunSyn : Funsyn.FUNSYN !*)
  module StateSyn : Statesyn.State.STATESYN

  exception Error of string

  val init : FunSyn.for_sml * StateSyn.order -> unit
end

(* signature MTPROVER *)
(* Meta Theorem Prover Version 1.3 *)

(* Author: Carsten Schuermann *)

module MTProver
    (MTPGlobal : Global.MTPGLOBAL)
    (StateSyn : Statesyn.State.STATESYN)
    (Order : Order.Order.ORDER)
    (MTPInit : Init.Mpi.MTPINIT)
    (MTPStrategy : Strategy.MTPSTRATEGY)
    (RelFun : Relfun.RELFUN) : Prover.PROVER = struct
  (*! structure IntSyn = IntSyn' !*)

  exception Error of string

  module I = IntSyn
  module F = FunSyn
  module S = StateSyn
  (* DISCLAIMER: This functor is temporary. Its purpose is to
       connect the new prover to Twelf  (see also functor below) *)

  (* List of open states *)

  let openStates : S.state list ref = ref []
  (* List of solved states *)

  let solvedStates : S.state list ref = ref []

  let rec transformOrder' = function
    | G, Order.Arg k ->
        let k' = I.ctxLength G - k + 1 in
        let (I.Dec (_, V)) = I.ctxDec (G, k') in
        S.Arg ((I.Root (I.BVar k', I.Nil), I.id), (V, I.id))
    | G, Order.Lex Os -> S.Lex (map (fun O -> transformOrder' (G, O)) Os)
    | G, Order.Simul Os -> S.Simul (map (fun O -> transformOrder' (G, O)) Os)

  let rec transformOrder = function
    | G, F.All (F.Prim D, F), Os ->
        S.All (D, transformOrder (I.Decl (G, D), F, Os))
    | G, F.And (F1, F2), O :: Os ->
        S.And (transformOrder (G, F1, [ O ]), transformOrder (G, F2, Os))
    | G, F.Ex _, [ O ] -> transformOrder' (G, O)
    | G, F.True, [ O ] -> transformOrder' (G, O)
  (* last case: no existentials---order must be trivial *)

  let rec select c = try Order.selLookup c with _ -> Order.Lex []
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

  let rec insertState S = openStates := S :: !openStates
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
    let _ = MTPGlobal.maxFill := k in
    let _ = reset () in
    let cL' = try Order.closure c with Order.Error _ -> cL in
    let F = RelFun.convertFor cL in
    let O = transformOrder (I.Null, F, map select cL) in
    if equiv (cL, cL') then
      List.app (fun S -> insertState S) (Mpi.MTPInit.init (F, O))
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
    let Open, solvedStates' =
      try MTPStrategy.run !openStates with
      | Splitting.Error s -> error ("Splitting Error: " ^ s)
      | Filling.Error s -> error ("Filling Error: " ^ s)
      | Recursion.Error s -> error ("Recursion Error: " ^ s)
      | Filling.TimeOut ->
          error "A proof could not be found -- Exceeding Time Limit\n"
    in
    let _ = openStates := Open in
    let _ = solvedStates := !solvedStates @ solvedStates' in
    if List.length !openStates > 0 then
      raise (Error "A proof could not be found")
    else ()

  let rec print () = ()
  let rec install _ = ()
  let init = init
  let auto = auto
  let print = print
  let install = install
  (* local *)
end

(* functor MTProver *)

module CombiProver
    (MTPGlobal : Global.MTPGLOBAL)
    (ProverOld : Prover.PROVER)
    (ProverNew : Prover.PROVER) : Prover.PROVER = struct
  (*! structure IntSyn = IntSyn' !*)

  exception Error of string

  let rec he f =
    try f () with
    | ProverNew.Error s -> raise (Error s)
    | ProverOld.Error s -> raise (Error s)

  let rec init Args =
    he (fun () ->
        match !MTPGlobal.prover with
        | MTPGlobal.New -> ProverNew.init Args
        | MTPGlobal.Old -> ProverOld.init Args)

  let rec auto Args =
    he (fun () ->
        match !MTPGlobal.prover with
        | MTPGlobal.New -> ProverNew.auto Args
        | MTPGlobal.Old -> ProverOld.auto Args)

  let rec print Args =
    he (fun () ->
        match !MTPGlobal.prover with
        | MTPGlobal.New -> ProverNew.print Args
        | MTPGlobal.Old -> ProverOld.print Args)

  let rec install Args =
    he (fun () ->
        match !MTPGlobal.prover with
        | MTPGlobal.New -> ProverNew.install Args
        | MTPGlobal.Old -> ProverOld.install Args)

  let init = init
  let auto = auto
  let print = print
  let install = install
  (* local *)
end

(* functor CombiProver *)
