functor Trace ((*! structure IntSyn' : INTSYN !*)
               structure Names : NAMES
               (*! sharing Names.IntSyn = IntSyn' !*)
               structure Whnf : WHNF
               (*! sharing Whnf.IntSyn = IntSyn' !*)
               structure Abstract : ABSTRACT
               (*! sharing Abstract.IntSyn = IntSyn' !*)
               structure Print : PRINT
               (*! sharing Print.IntSyn = IntSyn' !*)
                 )
  : TRACE =
struct

  (*! structure IntSyn = IntSyn' !*)

  local
    structure I = IntSyn
    structure P = Print
    structure N = Names

  in

    (* Printing Utilities *)

    fun headToString (G, I.Const (c)) = N.qidToString (N.constQid c)
      | (* GEN CASE BRANCH *) headToString (G, I.Def (d)) = N.qidToString (N.constQid d)
      | (* GEN CASE BRANCH *) headToString (G, I.BVar(k)) = N.bvarName (G, k)
    fun expToString (GU) = P.expToString (GU) ^ ". "
    fun decToString (GD) = P.decToString (GD) ^ ". "
    fun eqnToString (G, U1, U2) =
          P.expToString (G, U1) ^ " = " ^ P.expToString (G, U2) ^ ". "

    fun newline () = print "\n"

    fun printCtx (I.Null) = print "No hypotheses or parameters. "
      | (* GEN CASE BRANCH *) printCtx (I.Decl(I.Null, D)) =
          print (decToString (I.Null, D))
      | (* GEN CASE BRANCH *) printCtx (I.Decl(G, D)) =
          (printCtx (G);
           newline ();
           print (decToString (G, D)))

    fun evarsToString (Xnames) =
        let
          val inst = P.evarInstToString (Xnames)
          val constrOpt = P.evarCnstrsToStringOpt (Xnames)
        in
          case constrOpt
            of NONE => inst
             | SOME(constr) => inst ^ "\nConstraints:\n" ^ constr
        end

    fun varsToEVarInst (nil) = nil
      | (* GEN CASE BRANCH *) varsToEVarInst (name::names) =
        case N.getEVarOpt name
          of NONE => (print ("Trace warning: ignoring unknown variable " ^ name ^ "\n");
                      varsToEVarInst (names))
           | SOME(X) => (X,name)::varsToEVarInst (names)

    fun printVars (names) = print (evarsToString (varsToEVarInst names))

    fun printVarstring (line) =
          printVars (List.tl (String.tokens Char.isSpace line))

    datatype 'a spec =
        None
      | Some of 'a list
      | All

    val traceSpec : string spec ref = ref None
    val breakSpec : string spec ref = ref None

    fun trace (None) = traceSpec := None
      | (* GEN CASE BRANCH *) trace (Some (names)) = traceSpec := Some (names)
      | (* GEN CASE BRANCH *) trace (All) = traceSpec := All

    fun break (None) = breakSpec := None
      | (* GEN CASE BRANCH *) break (Some (names)) = breakSpec := Some (names)
      | (* GEN CASE BRANCH *) break (All) = breakSpec := All

    val detail = ref 1

    fun setDetail (NONE) = print ("Trace warning: detail is not a valid integer\n")
      | (* GEN CASE BRANCH *) setDetail (SOME(n)) =
        if 0 <= n (* andalso n <= 2 *)
          then detail := n
        else print ("Trace warning: detail must be positive\n")

    val traceTSpec : I.cid spec ref = ref None
    val breakTSpec : I.cid spec ref = ref None

    fun toCids (nil) = nil
      | (* GEN CASE BRANCH *) toCids (name::names) =
        (case N.stringToQid name
           of NONE => (print ("Trace warning: ignoring malformed qualified identifier " ^ name ^ "\n");
                       toCids names)
            | SOME qid =>
        (case N.constLookup qid
           of NONE => (print ("Trace warning: ignoring undeclared constant " ^ N.qidToString qid ^ "\n");
                       toCids names)
            | SOME cid => cid::toCids names))

    fun initTrace (None) = traceTSpec := None
      | (* GEN CASE BRANCH *) initTrace (Some (names)) = traceTSpec := Some (toCids names)
      | (* GEN CASE BRANCH *) initTrace (All) = traceTSpec := All

    fun initBreak (None) = breakTSpec := None
      | (* GEN CASE BRANCH *) initBreak (Some (names)) = breakTSpec := Some (toCids names)
      | (* GEN CASE BRANCH *) initBreak (All) = breakTSpec := All

    fun printHelp () =
        print
    "<newline> - continue --- execute with current settings\n\
    \n - next --- take a single step\n\
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
    \? for help"

    val currentGoal : (I.dctx * I.exp) ref =
          ref (I.Null, I.Uni (I.Type)) (* dummy initialization *)

    val currentEVarInst : (I.exp * string) list ref =
          ref nil

    fun setEVarInst (Xs) =
        currentEVarInst := List.map (fn X => (X, N.evarName (I.Null, X))) Xs

    fun setGoal (G, V) =
        (currentGoal := (G, V);
         setEVarInst (Abstract.collectEVars (G, (V, I.id), nil)))

    type goal_tag = int option

    val tag : goal_tag ref = ref NONE
    fun tagGoal () =
        case !tag
          of NONE => NONE
           | SOME(n) => (tag := SOME(n+1); !tag)

    val watchForTag : goal_tag ref = ref NONE

    fun initTag () =
        (watchForTag := NONE;
         case (!traceTSpec,!breakTSpec)
           of (None, None) => tag := NONE
            | _ => tag := SOME(0))

    fun setWatchForTag (NONE) = (watchForTag := !tag)
      | (* GEN CASE BRANCH *) setWatchForTag (SOME(n)) = (watchForTag := SOME(n))

    fun breakAction (G) =
        let
          val _ = print " "
          val line = Compat.inputLine97 (TextIO.stdIn)
        in
          case String.sub (line, 0)
            of #"\n" => ()
             | #"n" => (breakTSpec := All)
             | #"r" => (breakTSpec := None)
             | #"s" => (setWatchForTag (Int.fromString (String.extract (line, 1, NONE))))
             | #"t" => (traceTSpec := All;
                        print "% Now tracing all";
                        breakAction (G))
             | #"u" => (traceTSpec := None;
                        print "% Now tracing none";
                        breakAction (G))
             | #"d" => (setDetail (Int.fromString (String.extract (line, 1, NONE)));
                        print ("% Trace detail now " ^ Int.toString (!detail));
                        breakAction (G))
             | #"h" => (printCtx G; breakAction (G))
             | #"g" => (print (expToString (!currentGoal));
                        breakAction (G))
             | #"i" => (print (evarsToString (List.rev (!currentEVarInst)));
                        breakAction (G))
             | #"v" => (printVarstring (line); breakAction (G))
             | #"?" => (printHelp (); breakAction (G))
             | _ => (print "unrecognized command (? for help)";
                     breakAction (G))
        end

    fun init () =
        (initTrace (!traceSpec);
         initBreak (!breakSpec);
         initTag ())

    datatype event =
      IntroHyp of IntSyn.head * IntSyn.dec
    | DischargeHyp of IntSyn.head * IntSyn.dec

    | IntroParm of IntSyn.head * IntSyn.dec
    | DischargeParm of IntSyn.head * IntSyn.dec

    | Resolved of IntSyn.head * IntSyn.head (* resolved with clause c, fam a *)
    | Subgoal of (IntSyn.head * IntSyn.head) * (unit -> int) (* clause c, fam a, nth subgoal *)

    | SolveGoal of goal_tag * IntSyn.head * IntSyn.exp
    | SucceedGoal of goal_tag * (IntSyn.head * IntSyn.head) * IntSyn.exp
    | CommitGoal of goal_tag * (IntSyn.head * IntSyn.head) * IntSyn.exp
    | RetryGoal of goal_tag * (IntSyn.head * IntSyn.head) * IntSyn.exp (* clause c failed, fam a *)
    | FailGoal of goal_tag * IntSyn.head * IntSyn.exp

    | Unify of (IntSyn.head * IntSyn.head) * IntSyn.exp * IntSyn.exp (* clause head == goal *)
    | FailUnify of (IntSyn.head * IntSyn.head) * string (* failure message *)

    fun eventToString (G, IntroHyp (_, D)) =
        "% Introducing hypothesis\n" ^ decToString (G, D)
      | (* GEN CASE BRANCH *) eventToString (G, DischargeHyp (_, I.Dec (SOME(x), _))) =
        "% Discharging hypothesis " ^ x
      | (* GEN CASE BRANCH *) eventToString (G, IntroParm (_, D)) =
        "% Introducing parameter\n" ^ decToString (G, D)
      | (* GEN CASE BRANCH *) eventToString (G, DischargeParm (_, I.Dec (SOME(x), _))) =
        "% Discharging parameter " ^ x

      | (* GEN CASE BRANCH *) eventToString (G, Resolved (Hc, Ha)) =
        "% Resolved with clause " ^ headToString (G, Hc) ^ "\n"
        ^ evarsToString (List.rev (!currentEVarInst))
      | (* GEN CASE BRANCH *) eventToString (G, Subgoal ((Hc, Ha), msg)) =
        "% Solving subgoal (" ^ Int.toString (msg ()) ^ ") of clause "
        ^ headToString (G, Hc)

      | (* GEN CASE BRANCH *) eventToString (G, SolveGoal (SOME(tag), _, V)) =
        "% Goal " ^ Int.toString tag ^ ":\n" ^ expToString (G, V)
      | (* GEN CASE BRANCH *) eventToString (G, SucceedGoal (SOME(tag), _, V)) =
        "% Goal " ^ Int.toString tag ^ " succeeded"
      | (* GEN CASE BRANCH *) eventToString (G, CommitGoal (SOME(tag), _, V)) =
        "% Goal " ^ Int.toString tag ^ " committed to first solution"
      | (* GEN CASE BRANCH *) eventToString (G, RetryGoal (SOME(tag), (Hc, Ha), V)) =
        "% Backtracking from clause " ^ headToString (G, Hc) ^ "\n"
        ^ "% Retrying goal " ^ Int.toString tag ^ ":\n" ^ expToString (G, V)
      | (* GEN CASE BRANCH *) eventToString (G, FailGoal (SOME(tag), _, V)) =
        "% Failed goal " ^ Int.toString tag

      | (* GEN CASE BRANCH *) eventToString (G, Unify ((Hc, Ha), Q, P)) =
        "% Trying clause " ^ headToString (G, Hc) ^ "\n"
        ^ eqnToString (G, Q, P)
      | (* GEN CASE BRANCH *) eventToString (G, FailUnify ((Hc, Ha), msg)) =
        "% Unification failed with clause " ^ headToString (G, Hc) ^ ":\n"
        ^ msg

    fun traceEvent (G, e) = print (eventToString (G, e))

    fun monitorHead (cids, I.Const(c)) = List.exists (fn c' => c = c') cids
      | (* GEN CASE BRANCH *) monitorHead (cids, I.Def(d)) = List.exists (fn c' => d = c') cids
      | (* GEN CASE BRANCH *) monitorHead (cids, I.BVar(k)) = false

    fun monitorHeads (cids, (Hc, Ha)) =
          monitorHead (cids, Hc) orelse monitorHead (cids, Ha)

    fun monitorEvent (cids, IntroHyp (H, _)) =
          monitorHead (cids, H)
      | (* GEN CASE BRANCH *) monitorEvent (cids, DischargeHyp (H, _)) =
          monitorHead (cids, H)
      | (* GEN CASE BRANCH *) monitorEvent (cids, IntroParm (H, _)) =
          monitorHead (cids, H)
      | (* GEN CASE BRANCH *) monitorEvent (cids, DischargeParm (H, _)) =
          monitorHead (cids, H)

      | (* GEN CASE BRANCH *) monitorEvent (cids, SolveGoal (_, H, V)) =
          monitorHead (cids, H)
      | (* GEN CASE BRANCH *) monitorEvent (cids, SucceedGoal (_, (Hc, Ha), _)) =
          monitorHeads (cids, (Hc, Ha))
      | (* GEN CASE BRANCH *) monitorEvent (cids, CommitGoal (_, (Hc, Ha), _)) =
          monitorHeads (cids, (Hc, Ha))
      | (* GEN CASE BRANCH *) monitorEvent (cids, RetryGoal (_, (Hc, Ha), _)) =
          monitorHeads (cids, (Hc, Ha))
      | (* GEN CASE BRANCH *) monitorEvent (cids, FailGoal (_, H, _)) =
          monitorHead (cids, H)

      | (* GEN CASE BRANCH *) monitorEvent (cids, Resolved (Hc, Ha)) =
          monitorHeads (cids, (Hc, Ha))
      | (* GEN CASE BRANCH *) monitorEvent (cids, Subgoal ((Hc, Ha), _)) =
          monitorHeads (cids, (Hc, Ha))

      | (* GEN CASE BRANCH *) monitorEvent (cids, Unify ((Hc, Ha), _, _)) =
          monitorHeads (cids, (Hc, Ha))
      | (* GEN CASE BRANCH *) monitorEvent (cids, FailUnify ((Hc, Ha), _)) =
          monitorHeads (cids, (Hc, Ha))

    fun monitorDetail (Unify _) = !detail >= 2
      | (* GEN CASE BRANCH *) monitorDetail (FailUnify _) = !detail >= 2
      | (* GEN CASE BRANCH *) monitorDetail _ = !detail >= 1

    (* expensive if tracing Unify! *)
    (* but: maintain only if break or trace is on *)
    (* may not be sufficient for some information *)
    fun maintain (G, SolveGoal (_, _, V)) = setGoal (G, V)
      | (* GEN CASE BRANCH *) maintain (G, RetryGoal (_, _, V)) = setGoal (G, V)
      | (* GEN CASE BRANCH *) maintain (G, FailGoal (_, _, V)) = setGoal (G, V)
      | (* GEN CASE BRANCH *) maintain (G, Unify (_, Q, P)) =
        (* show substitution for variables in clause head if tracing unification *)
        setEVarInst (Abstract.collectEVars (G, (P, I.id),
                                            Abstract.collectEVars (G, (Q, I.id), nil)))
      | (* GEN CASE BRANCH *) maintain _ = ()

    fun monitorBreak (None, G, e) = false
      | (* GEN CASE BRANCH *) monitorBreak (Some (cids), G, e) =
        if monitorEvent (cids, e)
          then (maintain (G, e); traceEvent (G, e); breakAction (G); true)
        else false
      | (* GEN CASE BRANCH *) monitorBreak (All, G, e) =
          (maintain (G, e); traceEvent (G, e); breakAction (G); true)

    fun monitorTrace (None, G, e) = false
      | (* GEN CASE BRANCH *) monitorTrace (Some (cids), G, e) =
        if monitorEvent (cids, e)
          then (maintain (G, e); traceEvent (G, e); newline (); true)
        else false
      | (* GEN CASE BRANCH *) monitorTrace (All, G, e) =
          (maintain (G, e); traceEvent (G, e); newline (); true)

    fun watchFor (e) =
        case !watchForTag
          of NONE => false
           | SOME(t) => (case e
                           of SolveGoal (SOME(t'), _, _) => (t' = t)
                            | SucceedGoal (SOME(t'), _, _) => (t' = t)
                            | CommitGoal (SOME(t'), _, _) => (t' = t)
                            | RetryGoal (SOME(t'), _, _) => (t' = t)
                            | FailGoal (SOME(t'), _, _) => (t' = t)
                            | _ => false)

    fun skipping () =
        case !watchForTag
          of NONE => false
           | SOME _ => true

    fun signal (G, e) =
        if monitorDetail (e)
          then if skipping ()
                 then if watchFor (e)
                        then (watchForTag := NONE; signal (G, e))
                      else (monitorTrace (!traceTSpec, G, e); ())
               else if monitorBreak (!breakTSpec, G, e) (* stops, continues after input *)
                      then ()
                    else (monitorTrace (!traceTSpec, G, e); ()) (* prints trace, continues *)
        else ()

    fun showSpec (msg, None) = print (msg ^ " = None\n")
      | (* GEN CASE BRANCH *) showSpec (msg, Some(names)) =
        (print (msg ^ " = Some [");
         List.app (fn name => print (" " ^ name)) names;
         print "]\n")
      | (* GEN CASE BRANCH *) showSpec (msg, All) = print (msg ^ " = All\n")

    fun tracing () =
        (case (!traceSpec, !breakSpec)
           of (None, None) => false
            | _ => true)

    fun show () =
        (showSpec ("trace", !traceSpec);
         showSpec ("break", !breakSpec);
         print ("detail = " ^ Int.toString (!detail) ^ "\n"))

    fun reset () = (trace (None); break (None); detail := 1)
  end

end;  (* functor Trace *)
