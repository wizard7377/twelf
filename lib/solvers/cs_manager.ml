(* Constraint Solver Manager *)

(* Author: Roberto Virga *)

module type CS_MANAGER = sig
  (* structure IntSyn : INTSYN *)
  module Fixity : FIXITY

  (*! structure ModeSyn : MODESYN !*)
  type sigEntry =
    (* global signature entry *)
    (* constant declaration plus optional precedence and mode information *)
    IntSyn.conDec * Fixity.fixity option * ModeSyn.modeSpine list

  type fgnConDec =
    (* foreign constant declaration *)
    < parse : string -> IntSyn.conDec option >

  type solver =
    (* constraint solver *)
    < (* name is the name of the solver *)
    name : string (* keywords identifying the type of solver *)
    ; (* NOTE: no two solvers with the same keywords may be active simultaneously *)
    keywords : string (* names of other constraint solvers needed *)
    ; needs : string list (* foreign constants declared (if any) *)
    ; fgnConst : fgnConDec option (* install constants *)
    ; init : int * (sigEntry -> IntSyn.cid) -> unit (* reset internal status *)
    ; reset : unit -> unit (* trailing operations *)
    ; mark : unit -> unit
    ; unwind : unit -> unit >

  exception Error of string

  (* solver handling functions *)
  val setInstallFN : (sigEntry -> IntSyn.cid) -> unit
  val installSolver : solver -> IntSyn.csid
  val resetSolvers : unit -> unit
  val useSolver : string -> unit

  (* parsing foreign constatnts *)
  val parse : string -> IntSyn.csid * IntSyn.conDec option

  (* trailing operations *)
  val reset : unit -> unit
  val trail : (unit -> 'a) -> 'a
end

(* signature CS_MANAGER *)
(* Constraint Solver Manager *)

(* Author: Roberto Virga *)

module CSManager (Global : GLOBAL) (Unify : UNIFY) (Fixity : FIXITY) :
  CS_MANAGER = struct
  module IntSyn = IntSyn
  module Fixity = Fixity
  (* structure ModeSyn = ModeSyn *)

  type sigEntry =
    (* global signature entry *)
    (* constant declaration plus optional precedence and mode information *)
    IntSyn.conDec * Fixity.fixity option * ModeSyn.modeSpine list

  type fgnConDec =
    (* foreign constant declaration *)
    < parse : string -> IntSyn.conDec option >

  type solver =
    (* constraint solver *)
    < (* name is the name of the solver *)
    name : string (* keywords identifying the type of solver *)
    ; (* NOTE: no two solvers with the same keywords may be active simultaneously *)
    keywords : string (* names of other constraint solvers needed *)
    ; needs : string list (* foreign constants declared (if any) *)
    ; fgnConst : fgnConDec option (* install constants *)
    ; init : int * (sigEntry -> IntSyn.cid) -> unit (* reset internal status *)
    ; reset : unit -> unit (* trailing operations *)
    ; mark : unit -> unit
    ; unwind : unit -> unit >

  exception Error of string
  (* vacuous solver *)

  let emptySolver =
    {
      name = "";
      keywords = "";
      needs = [];
      fgnConst = None;
      init = (fun _ -> ());
      reset = (fun () -> ());
      mark = (fun () -> ());
      unwind = (fun () -> ());
    }
  (* Twelf a constraint solver *)

  let unifySolver =
    {
      name = "Unify";
      keywords = "unification";
      needs = [];
      fgnConst = None;
      init = (fun _ -> ());
      reset = Unify.reset;
      mark = Unify.mark;
      unwind = Unify.unwind;
    }
  (* List of installed solvers *)

  type solver = Solver of solver * bool ref

  let maxCS = Global.maxCSid

  let csArray =
    (Array.array (maxCS + 1, Solver (emptySolver, ref false))
      : solver Array.array)

  let _ = Array.update (csArray, 0, Solver (unifySolver, ref true))
  let nextCS = (ref 1 : int ref)
  (* Installing function *)

  let installFN = (ref (fun _ -> -1) : sigEntry -> IntSyn.cid ref)
  let rec setInstallFN f = installFN := f
  (* install the specified solver *)

  let rec installSolver solver =
    (* val _ = print ("Installing constraint domain " ^ #name solver ^ "\n") *)
    let cs = !nextCS in
    let _ =
      if !nextCS > maxCS then raise (Error "too many constraint solvers")
      else ()
    in
    let _ = Array.update (csArray, cs, Solver (solver, ref false)) in
    let _ = nextCS := !nextCS + 1 in
    cs
  (* install the unification solver *)

  let _ = installSolver unifySolver
  let activeKeywords = (ref [] : string list ref)
  (* make all the solvers inactive *)

  let rec resetSolvers () =
    ArraySlice.appi
      (fun (cs, Solver (solver, active)) ->
        if !active then (
          active := false;
          reset solver ())
        else ())
      (ArraySlice.slice (csArray, 0, Some !nextCS));
    activeKeywords := [];
    useSolver "Unify"

  and useSolver name =
    let exception Found of IntSyn.csid in
    let rec findSolver name =
      try
        ArraySlice.appi
          (fun (cs, Solver (solver, _)) ->
            if name solver = name then raise (Found cs) else ())
          (ArraySlice.slice (csArray, 0, Some !nextCS));
        None
      with Found cs -> Some cs
    in
    match findSolver name with
    | Some cs ->
        let (Solver (solver, active)) = Array.sub (csArray, cs) in
        if !active then ()
        else if List.exists (fun s -> s = keywords solver) !activeKeywords then
          raise
            (Error
               ("solver " ^ name
              ^ " is incompatible with a currently active solver"))
        else (
          active := true;
          activeKeywords := keywords solver :: !activeKeywords;
          List.app useSolver (needs solver);
          init solver (cs, !installFN))
    | None -> raise (Error ("solver " ^ name ^ " not found"))
  (* ask each active solver to try and parse the given string *)

  let rec parse string =
    let exception Parsed of IntSyn.csid * IntSyn.conDec in
    let rec parse' ((cs, solver) : solver) =
      match fgnConst solver with
      | None -> ()
      | Some fgnConDec -> (
          match parse fgnConDec string with
          | None -> ()
          | Some conDec -> raise (Parsed (cs, conDec)))
    in
    try
      ArraySlice.appi
        (fun (cs, Solver (solver, active)) ->
          if !active then parse' (cs, solver) else ())
        (ArraySlice.slice (csArray, 0, Some !nextCS));
      None
    with Parsed info -> Some info

  let markCount = (ref 0 : int ref)
  (* reset the internal status of all the active solvers *)

  let rec reset () =
    ArraySlice.appi
      (fun (_, Solver (solver, active)) ->
        if !active then (
          markCount := 0;
          reset solver ())
        else ())
      (ArraySlice.slice (csArray, 0, Some !nextCS))
  (* mark all active solvers *)

  let rec mark () =
    markCount := !markCount + 1;
    ArraySlice.appi
      (fun (_, Solver (solver, active)) ->
        if !active then mark solver () else ())
      (ArraySlice.slice (csArray, 0, Some !nextCS))
  (* unwind all active solvers *)

  let rec unwind targetCount =
    let rec unwind' = function
      | 0 -> markCount := targetCount
      | k ->
          ArraySlice.appi
            (fun (_, Solver (solver, active)) ->
              if !active then unwind solver () else ())
            (ArraySlice.slice (csArray, 0, Some !nextCS));
          unwind' (k - 1)
    in
    unwind' (!markCount - targetCount)
  (* trail the give function *)

  let rec trail f =
    let current = !markCount in
    let _ = mark () in
    let r = f () in
    let _ = unwind current in
    r

  let setInstallFN = setInstallFN
  let installSolver = installSolver
  let resetSolvers = resetSolvers
  let useSolver = useSolver
  let parse = parse
  let reset = reset
  let trail = trail
end

(* functor CSManager *)

module CSManager =
  CSManager
    (struct
      module Global = Global
    end)
    (struct
      module Unify = UnifyTrail
    end)
    (struct
      module Fixity = NamesFixity
    end)
