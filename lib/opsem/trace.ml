open Basis ;; 

module type TRACE = sig
  (* Program interface *)
  (*! structure IntSyn : Intsyn.INTSYN !*)
  type goalTag

  val tagGoal : unit -> goalTag

  type event =
    | IntroHyp of IntSyn.head * IntSyn.dec
    | DischargeHyp of IntSyn.head * IntSyn.dec
    | IntroParm of IntSyn.head * IntSyn.dec
    | DischargeParm of IntSyn.head * IntSyn.dec
    | Resolved of IntSyn.head * IntSyn.head
    | Subgoal of (IntSyn.head * IntSyn.head) * (unit -> int)
    | SolveGoal of goalTag * IntSyn.head * IntSyn.exp
    | SucceedGoal of goalTag * (IntSyn.head * IntSyn.head) * IntSyn.exp
    | CommitGoal of goalTag * (IntSyn.head * IntSyn.head) * IntSyn.exp
    | RetryGoal of goalTag * (IntSyn.head * IntSyn.head) * IntSyn.exp
    | FailGoal of goalTag * IntSyn.head * IntSyn.exp
    | Unify of (IntSyn.head * IntSyn.head) * IntSyn.exp * IntSyn.exp
    | FailUnify of (IntSyn.head * IntSyn.head) * string

  (* failure message *)
  val signal : IntSyn.dctx * event -> unit
  val init : unit -> unit

  (* initialize trace, break and tag *)
  val tracing : unit -> bool

  (* currently tracing or using breakpoints *)
  (* User interface *)
  type 'a spec = None | Some of 'a list | All

  val trace : string spec -> unit
  val break : string spec -> unit
  val detail : int ref

  (* 0 = none, 1 = default, 2 = unify *)
  val show : unit -> unit

  (* show trace, break, detail *)
  val reset : unit -> unit
  (* reset trace, break, detail *)
end

(* signature TRACE *)
module Trace
    (Names : Names.NAMES)
    (Whnf : Whnf.WHNF)
    (Abstract : Abstract.ABSTRACT)
    (Print : Print.PRINT) : TRACE = struct
  (*! structure IntSyn = IntSyn' !*)

  module I = IntSyn
  module P = Print
  module N = Names
  (* Printing Utilities *)

  let rec headToString = function
    | G, I.Const c -> N.qidToString (N.constQid c)
    | G, I.Def d -> N.qidToString (N.constQid d)
    | G, I.BVar k -> N.bvarName (G, k)

  let rec expToString GU = P.expToString GU ^ ". "
  let rec decToString GD = P.decToString GD ^ ". "

  let rec eqnToString (G, U1, U2) =
    P.expToString (G, U1) ^ " = " ^ P.expToString (G, U2) ^ ". "

  let rec newline () = print "\n"

  let rec printCtx = function
    | I.Null -> print "No hypotheses or parameters. "
    | I.Decl (I.Null, D) -> print (decToString (I.Null, D))
    | I.Decl (G, D) ->
        printCtx G;
        newline ();
        print (decToString (G, D))

  let rec evarsToString Xnames =
    let inst = P.evarInstToString Xnames in
    let constrOpt = P.evarCnstrsToStringOpt Xnames in
    match constrOpt with
    | None -> inst
    | Some constr -> inst ^ "\nConstraints:\n" ^ constr

  let rec varsToEVarInst = function
    | [] -> []
    | name :: names -> (
        match N.getEVarOpt name with
        | None ->
            print ("Trace warning: ignoring unknown variable " ^ name ^ "\n");
            varsToEVarInst names
        | Some X -> (X, name) :: varsToEVarInst names)

  let rec printVars names = print (evarsToString (varsToEVarInst names))

  let rec printVarstring line =
    printVars (List.tl (String.tokens Char.isSpace line))

  type 'a spec = None | Some of 'a list | All

  let traceSpec : string spec ref = ref None
  let breakSpec : string spec ref = ref None

  let rec trace = function
    | None -> traceSpec := None
    | Some names -> traceSpec := Some names
    | All -> traceSpec := All

  let rec break = function
    | None -> breakSpec := None
    | Some names -> breakSpec := Some names
    | All -> breakSpec := All

  let detail = ref 1

  let rec setDetail = function
    | None -> print "Trace warning: detail is not a valid integer\n"
    | Some n ->
        if 0 <= n (* andalso n <= 2 *) then detail := n
        else print "Trace warning: detail must be positive\n"

  let traceTSpec : I.cid spec ref = ref None
  let breakTSpec : I.cid spec ref = ref None

  let rec toCids = function
    | [] -> []
    | name :: names -> (
        match N.stringToQid name with
        | None ->
            print
              ("Trace warning: ignoring malformed qualified identifier " ^ name
             ^ "\n");
            toCids names
        | Some qid -> (
            match N.constLookup qid with
            | None ->
                print
                  ("Trace warning: ignoring undeclared constant "
                 ^ N.qidToString qid ^ "\n");
                toCids names
            | Some cid -> cid :: toCids names))

  let rec initTrace = function
    | None -> traceTSpec := None
    | Some names -> traceTSpec := Some (toCids names)
    | All -> traceTSpec := All

  let rec initBreak = function
    | None -> breakTSpec := None
    | Some names -> breakTSpec := Some (toCids names)
    | All -> breakTSpec := All

  let rec printHelp () =
    print
      "<newline> - continue --- execute with current settings\n\n\
      \ - next --- take a single step\n\
       \r - run --- remove all breakpoints and continue\n\
       \s - skip --- skip until current subgoals succeeds, is retried, or fails\n\
       \s n - skip to n --- skip until goal (n) is considered\n\
       \t - trace --- trace all events\n\
       \u - untrace --- trace no events\n\
       \d n - detail --- set trace detail to n (0, 1, or 2)\n\
       \h - hypotheses --- show current hypotheses\n\
       \g - goal --- show current goal\n\
       \i - instantiation --- show instantiation of variables in current goal\n\
       \v X1 ... Xn - variables --- show instantiation of X1 ... Xn\n\
       \? for_sml help"

  let currentGoal : I.dctx * I.exp ref = ref (I.Null, I.Uni I.Type)
  (* dummy initialization *)

  let currentEVarInst : I.exp * string list ref = ref []

  let rec setEVarInst Xs =
    currentEVarInst := List.map (fun X -> (X, N.evarName (I.Null, X))) Xs

  let rec setGoal (G, V) =
    currentGoal := (G, V);
    setEVarInst (Abstract.collectEVars (G, (V, I.id), []))

  type goalTag = int option

  let tag : goalTag ref = ref None

  let rec tagGoal () =
    match !tag with
    | None -> None
    | Some n ->
        tag := Some (n + 1);
        !tag

  let watchForTag : goalTag ref = ref None

  let rec initTag () =
    watchForTag := None;
    match (!traceTSpec, !breakTSpec) with
    | None, None -> tag := None
    | _ -> tag := Some 0

  let rec setWatchForTag = function
    | None -> watchForTag := !tag
    | Some n -> watchForTag := Some n

  let rec breakAction G =
    let _ = print " " in
    let line = Compat.inputLine97 TextIO.stdIn in
    match String.sub (line, 0) with
    | '\n' -> ()
    | 'n' -> breakTSpec := All
    | 'r' -> breakTSpec := None
    | 's' -> setWatchForTag (Int.fromString (String.extract (line, 1, None)))
    | 't' ->
        traceTSpec := All;
        print "% Now tracing all";
        breakAction G
    | 'u' ->
        traceTSpec := None;
        print "% Now tracing none";
        breakAction G
    | 'd' ->
        setDetail (Int.fromString (String.extract (line, 1, None)));
        print ("% Trace detail now " ^ Int.toString !detail);
        breakAction G
    | 'h' ->
        printCtx G;
        breakAction G
    | 'g' ->
        print (expToString !currentGoal);
        breakAction G
    | 'i' ->
        print (evarsToString (List.rev !currentEVarInst));
        breakAction G
    | 'v' ->
        printVarstring line;
        breakAction G
    | '?' ->
        printHelp ();
        breakAction G
    | _ ->
        print "unrecognized command (? for_sml help)";
        breakAction G

  let rec init () =
    initTrace !traceSpec;
    initBreak !breakSpec;
    initTag ()

  type event =
    | IntroHyp of IntSyn.head * IntSyn.dec
    | DischargeHyp of IntSyn.head * IntSyn.dec
    | IntroParm of IntSyn.head * IntSyn.dec
    | DischargeParm of IntSyn.head * IntSyn.dec
    | Resolved of IntSyn.head * IntSyn.head
    | Subgoal of (IntSyn.head * IntSyn.head) * (unit -> int)
    | SolveGoal of goalTag * IntSyn.head * IntSyn.exp
    | SucceedGoal of goalTag * (IntSyn.head * IntSyn.head) * IntSyn.exp
    | CommitGoal of goalTag * (IntSyn.head * IntSyn.head) * IntSyn.exp
    | RetryGoal of goalTag * (IntSyn.head * IntSyn.head) * IntSyn.exp
    | FailGoal of goalTag * IntSyn.head * IntSyn.exp
    | Unify of (IntSyn.head * IntSyn.head) * IntSyn.exp * IntSyn.exp
    | FailUnify of (IntSyn.head * IntSyn.head) * string
  (* failure message *)

  let rec eventToString = function
    | G, IntroHyp (_, D) -> "% Introducing hypothesis\n" ^ decToString (G, D)
    | G, DischargeHyp (_, I.Dec (Some x, _)) -> "% Discharging hypothesis " ^ x
    | G, IntroParm (_, D) -> "% Introducing parameter\n" ^ decToString (G, D)
    | G, DischargeParm (_, I.Dec (Some x, _)) -> "% Discharging parameter " ^ x
    | G, Resolved (Hc, Ha) ->
        "% Resolved with clause "
        ^ headToString (G, Hc)
        ^ "\n"
        ^ evarsToString (List.rev !currentEVarInst)
    | G, Subgoal ((Hc, Ha), msg) ->
        "% Solving subgoal ("
        ^ Int.toString (msg ())
        ^ ") of clause "
        ^ headToString (G, Hc)
    | G, SolveGoal (Some tag, _, V) ->
        "% Goal " ^ Int.toString tag ^ ":\n" ^ expToString (G, V)
    | G, SucceedGoal (Some tag, _, V) ->
        "% Goal " ^ Int.toString tag ^ " succeeded"
    | G, CommitGoal (Some tag, _, V) ->
        "% Goal " ^ Int.toString tag ^ " committed to first solution"
    | G, RetryGoal (Some tag, (Hc, Ha), V) ->
        "% Backtracking from clause "
        ^ headToString (G, Hc)
        ^ "\n" ^ "% Retrying goal " ^ Int.toString tag ^ ":\n"
        ^ expToString (G, V)
    | G, FailGoal (Some tag, _, V) -> "% Failed goal " ^ Int.toString tag
    | G, Unify ((Hc, Ha), Q, P) ->
        "% Trying clause " ^ headToString (G, Hc) ^ "\n" ^ eqnToString (G, Q, P)
    | G, FailUnify ((Hc, Ha), msg) ->
        "% Unification failed with clause " ^ headToString (G, Hc) ^ ":\n" ^ msg

  let rec traceEvent (G, e) = print (eventToString (G, e))

  let rec monitorHead = function
    | cids, I.Const c -> List.exists (fun c' -> c = c') cids
    | cids, I.Def d -> List.exists (fun c' -> d = c') cids
    | cids, I.BVar k -> false

  let rec monitorHeads (cids, (Hc, Ha)) =
    monitorHead (cids, Hc) || monitorHead (cids, Ha)

  let rec monitorEvent = function
    | cids, IntroHyp (H, _) -> monitorHead (cids, H)
    | cids, DischargeHyp (H, _) -> monitorHead (cids, H)
    | cids, IntroParm (H, _) -> monitorHead (cids, H)
    | cids, DischargeParm (H, _) -> monitorHead (cids, H)
    | cids, SolveGoal (_, H, V) -> monitorHead (cids, H)
    | cids, SucceedGoal (_, (Hc, Ha), _) -> monitorHeads (cids, (Hc, Ha))
    | cids, CommitGoal (_, (Hc, Ha), _) -> monitorHeads (cids, (Hc, Ha))
    | cids, RetryGoal (_, (Hc, Ha), _) -> monitorHeads (cids, (Hc, Ha))
    | cids, FailGoal (_, H, _) -> monitorHead (cids, H)
    | cids, Resolved (Hc, Ha) -> monitorHeads (cids, (Hc, Ha))
    | cids, Subgoal ((Hc, Ha), _) -> monitorHeads (cids, (Hc, Ha))
    | cids, Unify ((Hc, Ha), _, _) -> monitorHeads (cids, (Hc, Ha))
    | cids, FailUnify ((Hc, Ha), _) -> monitorHeads (cids, (Hc, Ha))

  let rec monitorDetail = function
    | Unify _ -> !detail >= 2
    | FailUnify _ -> !detail >= 2
    | _ -> !detail >= 1
  (* expensive if tracing Unify! *)

  (* but: maintain only if break or trace is on *)

  (* may not be sufficient for_sml some information *)

  let rec maintain = function
    | G, SolveGoal (_, _, V) -> setGoal (G, V)
    | G, RetryGoal (_, _, V) -> setGoal (G, V)
    | G, FailGoal (_, _, V) -> setGoal (G, V)
    | G, Unify (_, Q, P) ->
        setEVarInst
          (Abstract.collectEVars
             (G, (P, I.id), Abstract.collectEVars (G, (Q, I.id), [])))
    | _ -> ()

  let rec monitorBreak = function
    | None, G, e -> false
    | Some cids, G, e ->
        if monitorEvent (cids, e) then (
          maintain (G, e);
          traceEvent (G, e);
          breakAction G;
          true)
        else false
    | All, G, e ->
        maintain (G, e);
        traceEvent (G, e);
        breakAction G;
        true

  let rec monitorTrace = function
    | None, G, e -> false
    | Some cids, G, e ->
        if monitorEvent (cids, e) then (
          maintain (G, e);
          traceEvent (G, e);
          newline ();
          true)
        else false
    | All, G, e ->
        maintain (G, e);
        traceEvent (G, e);
        newline ();
        true

  let rec watchFor e =
    match !watchForTag with
    | None -> false
    | Some t -> (
        match e with
        | SolveGoal (Some t', _, _) -> t' = t
        | SucceedGoal (Some t', _, _) -> t' = t
        | CommitGoal (Some t', _, _) -> t' = t
        | RetryGoal (Some t', _, _) -> t' = t
        | FailGoal (Some t', _, _) -> t' = t
        | _ -> false)

  let rec skipping () = match !watchForTag with None -> false | Some _ -> true

  let rec signal (G, e) =
    if monitorDetail e then
      if skipping () then
        if watchFor e then (
          watchForTag := None;
          signal (G, e))
        else (
          monitorTrace (!traceTSpec, G, e);
          ())
      else if
        monitorBreak (!breakTSpec, G, e)
        (* stops, continues after input *)
      then ()
      else (
        monitorTrace (!traceTSpec, G, e);
        () (* prints trace, continues *))
    else ()

  let rec showSpec = function
    | msg, None -> print (msg ^ " = None\n")
    | msg, Some names ->
        print (msg ^ " = Some [");
        List.app (fun name -> print (" " ^ name)) names;
        print "]\n"
    | msg, All -> print (msg ^ " = All\n")

  let rec tracing () =
    match (!traceSpec, !breakSpec) with None, None -> false | _ -> true

  let rec show () =
    showSpec ("trace", !traceSpec);
    showSpec ("break", !breakSpec);
    print ("detail = " ^ Int.toString !detail ^ "\n")

  let rec reset () =
    trace None;
    break None;
    detail := 1
end

(* functor Trace *)
