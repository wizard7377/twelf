functor (* GEN BEGIN FUNCTOR DECL *) Trace ((*! structure IntSyn' : INTSYN !*)
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

    fun (* GEN BEGIN FUN FIRST *) headToString (G, I.Const (c)) = N.qidToString (N.constQid c) (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) headToString (G, I.Def (d)) = N.qidToString (N.constQid d) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) headToString (G, I.BVar(k)) = N.bvarName (G, k) (* GEN END FUN BRANCH *)
    fun expToString (GU) = P.expToString (GU) ^ ". "
    fun decToString (GD) = P.decToString (GD) ^ ". "
    fun eqnToString (G, U1, U2) =
          P.expToString (G, U1) ^ " = " ^ P.expToString (G, U2) ^ ". "

    fun newline () = print "\n"

    fun (* GEN BEGIN FUN FIRST *) printCtx (I.Null) = print "No hypotheses or parameters. " (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) printCtx (I.Decl(I.Null, D)) =
          print (decToString (I.Null, D)) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) printCtx (I.Decl(G, D)) =
          (printCtx (G);
           newline ();
           print (decToString (G, D))) (* GEN END FUN BRANCH *)

    fun evarsToString (Xnames) =
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val inst = P.evarInstToString (Xnames) (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val constrOpt = P.evarCnstrsToStringOpt (Xnames) (* GEN END TAG OUTSIDE LET *)
        in
          case constrOpt
            of NONE => inst
             | SOME(constr) => inst ^ "\nConstraints:\n" ^ constr
        end

    fun (* GEN BEGIN FUN FIRST *) varsToEVarInst (nil) = nil (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) varsToEVarInst (name::names) =
        case N.getEVarOpt name
          of NONE => (print ("Trace warning: ignoring unknown variable " ^ name ^ "\n");
                      varsToEVarInst (names))
           | SOME(X) => (X,name)::varsToEVarInst (names) (* GEN END FUN BRANCH *)

    fun printVars (names) = print (evarsToString (varsToEVarInst names))

    fun printVarstring (line) =
          printVars (List.tl (String.tokens Char.isSpace line))

    datatype 'a spec =
        None
      | Some of 'a list
      | All

    (* GEN BEGIN TAG OUTSIDE LET *) val traceSpec : string spec ref = ref None (* GEN END TAG OUTSIDE LET *)
    (* GEN BEGIN TAG OUTSIDE LET *) val breakSpec : string spec ref = ref None (* GEN END TAG OUTSIDE LET *)

    fun (* GEN BEGIN FUN FIRST *) trace (None) = traceSpec := None (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) trace (Some (names)) = traceSpec := Some (names) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) trace (All) = traceSpec := All (* GEN END FUN BRANCH *)

    fun (* GEN BEGIN FUN FIRST *) break (None) = breakSpec := None (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) break (Some (names)) = breakSpec := Some (names) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) break (All) = breakSpec := All (* GEN END FUN BRANCH *)

    (* GEN BEGIN TAG OUTSIDE LET *) val detail = ref 1 (* GEN END TAG OUTSIDE LET *)

    fun (* GEN BEGIN FUN FIRST *) setDetail (NONE) = print ("Trace warning: detail is not a valid integer\n") (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) setDetail (SOME(n)) =
        if 0 <= n (* andalso n <= 2 *)
          then detail := n
        else print ("Trace warning: detail must be positive\n") (* GEN END FUN BRANCH *)

    (* GEN BEGIN TAG OUTSIDE LET *) val traceTSpec : I.cid spec ref = ref None (* GEN END TAG OUTSIDE LET *)
    (* GEN BEGIN TAG OUTSIDE LET *) val breakTSpec : I.cid spec ref = ref None (* GEN END TAG OUTSIDE LET *)

    fun (* GEN BEGIN FUN FIRST *) toCids (nil) = nil (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) toCids (name::names) =
        (case N.stringToQid name
           of NONE => (print ("Trace warning: ignoring malformed qualified identifier " ^ name ^ "\n");
                       toCids names)
            | SOME qid =>
        (case N.constLookup qid
           of NONE => (print ("Trace warning: ignoring undeclared constant " ^ N.qidToString qid ^ "\n");
                       toCids names)
            | SOME cid => cid::toCids names)) (* GEN END FUN BRANCH *)

    fun (* GEN BEGIN FUN FIRST *) initTrace (None) = traceTSpec := None (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) initTrace (Some (names)) = traceTSpec := Some (toCids names) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) initTrace (All) = traceTSpec := All (* GEN END FUN BRANCH *)

    fun (* GEN BEGIN FUN FIRST *) initBreak (None) = breakTSpec := None (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) initBreak (Some (names)) = breakTSpec := Some (toCids names) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) initBreak (All) = breakTSpec := All (* GEN END FUN BRANCH *)

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

    (* GEN BEGIN TAG OUTSIDE LET *) val currentGoal : (I.dctx * I.exp) ref =
          ref (I.Null, I.Uni (I.Type)) (* GEN END TAG OUTSIDE LET *) (* dummy initialization *)

    (* GEN BEGIN TAG OUTSIDE LET *) val currentEVarInst : (I.exp * string) list ref =
          ref nil (* GEN END TAG OUTSIDE LET *)

    fun setEVarInst (Xs) =
        currentEVarInst := List.map ((* GEN BEGIN FUNCTION EXPRESSION *) fn X => (X, N.evarName (I.Null, X)) (* GEN END FUNCTION EXPRESSION *)) Xs

    fun setGoal (G, V) =
        (currentGoal := (G, V);
         setEVarInst (Abstract.collectEVars (G, (V, I.id), nil)))

    type goal_tag = int option

    (* GEN BEGIN TAG OUTSIDE LET *) val tag : goal_tag ref = ref NONE (* GEN END TAG OUTSIDE LET *)
    fun tagGoal () =
        case !tag
          of NONE => NONE
           | SOME(n) => (tag := SOME(n+1); !tag)

    (* GEN BEGIN TAG OUTSIDE LET *) val watchForTag : goal_tag ref = ref NONE (* GEN END TAG OUTSIDE LET *)

    fun initTag () =
        (watchForTag := NONE;
         case (!traceTSpec,!breakTSpec)
           of (None, None) => tag := NONE
            | _ => tag := SOME(0))

    fun (* GEN BEGIN FUN FIRST *) setWatchForTag (NONE) = (watchForTag := !tag) (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) setWatchForTag (SOME(n)) = (watchForTag := SOME(n)) (* GEN END FUN BRANCH *)

    fun breakAction (G) =
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val _ = print " " (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val line = Compat.inputLine97 (TextIO.stdIn) (* GEN END TAG OUTSIDE LET *)
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

    fun (* GEN BEGIN FUN FIRST *) eventToString (G, IntroHyp (_, D)) =
        "% Introducing hypothesis\n" ^ decToString (G, D) (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) eventToString (G, DischargeHyp (_, I.Dec (SOME(x), _))) =
        "% Discharging hypothesis " ^ x (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) eventToString (G, IntroParm (_, D)) =
        "% Introducing parameter\n" ^ decToString (G, D) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) eventToString (G, DischargeParm (_, I.Dec (SOME(x), _))) =
        "% Discharging parameter " ^ x (* GEN END FUN BRANCH *)

      | (* GEN BEGIN FUN BRANCH *) eventToString (G, Resolved (Hc, Ha)) =
        "% Resolved with clause " ^ headToString (G, Hc) ^ "\n"
        ^ evarsToString (List.rev (!currentEVarInst)) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) eventToString (G, Subgoal ((Hc, Ha), msg)) =
        "% Solving subgoal (" ^ Int.toString (msg ()) ^ ") of clause "
        ^ headToString (G, Hc) (* GEN END FUN BRANCH *)

      | (* GEN BEGIN FUN BRANCH *) eventToString (G, SolveGoal (SOME(tag), _, V)) =
        "% Goal " ^ Int.toString tag ^ ":\n" ^ expToString (G, V) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) eventToString (G, SucceedGoal (SOME(tag), _, V)) =
        "% Goal " ^ Int.toString tag ^ " succeeded" (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) eventToString (G, CommitGoal (SOME(tag), _, V)) =
        "% Goal " ^ Int.toString tag ^ " committed to first solution" (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) eventToString (G, RetryGoal (SOME(tag), (Hc, Ha), V)) =
        "% Backtracking from clause " ^ headToString (G, Hc) ^ "\n"
        ^ "% Retrying goal " ^ Int.toString tag ^ ":\n" ^ expToString (G, V) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) eventToString (G, FailGoal (SOME(tag), _, V)) =
        "% Failed goal " ^ Int.toString tag (* GEN END FUN BRANCH *)

      | (* GEN BEGIN FUN BRANCH *) eventToString (G, Unify ((Hc, Ha), Q, P)) =
        "% Trying clause " ^ headToString (G, Hc) ^ "\n"
        ^ eqnToString (G, Q, P) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) eventToString (G, FailUnify ((Hc, Ha), msg)) =
        "% Unification failed with clause " ^ headToString (G, Hc) ^ ":\n"
        ^ msg (* GEN END FUN BRANCH *)

    fun traceEvent (G, e) = print (eventToString (G, e))

    fun (* GEN BEGIN FUN FIRST *) monitorHead (cids, I.Const(c)) = List.exists ((* GEN BEGIN FUNCTION EXPRESSION *) fn c' => c = c' (* GEN END FUNCTION EXPRESSION *)) cids (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) monitorHead (cids, I.Def(d)) = List.exists ((* GEN BEGIN FUNCTION EXPRESSION *) fn c' => d = c' (* GEN END FUNCTION EXPRESSION *)) cids (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) monitorHead (cids, I.BVar(k)) = false (* GEN END FUN BRANCH *)

    fun monitorHeads (cids, (Hc, Ha)) =
          monitorHead (cids, Hc) orelse monitorHead (cids, Ha)

    fun (* GEN BEGIN FUN FIRST *) monitorEvent (cids, IntroHyp (H, _)) =
          monitorHead (cids, H) (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) monitorEvent (cids, DischargeHyp (H, _)) =
          monitorHead (cids, H) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) monitorEvent (cids, IntroParm (H, _)) =
          monitorHead (cids, H) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) monitorEvent (cids, DischargeParm (H, _)) =
          monitorHead (cids, H) (* GEN END FUN BRANCH *)

      | (* GEN BEGIN FUN BRANCH *) monitorEvent (cids, SolveGoal (_, H, V)) =
          monitorHead (cids, H) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) monitorEvent (cids, SucceedGoal (_, (Hc, Ha), _)) =
          monitorHeads (cids, (Hc, Ha)) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) monitorEvent (cids, CommitGoal (_, (Hc, Ha), _)) =
          monitorHeads (cids, (Hc, Ha)) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) monitorEvent (cids, RetryGoal (_, (Hc, Ha), _)) =
          monitorHeads (cids, (Hc, Ha)) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) monitorEvent (cids, FailGoal (_, H, _)) =
          monitorHead (cids, H) (* GEN END FUN BRANCH *)

      | (* GEN BEGIN FUN BRANCH *) monitorEvent (cids, Resolved (Hc, Ha)) =
          monitorHeads (cids, (Hc, Ha)) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) monitorEvent (cids, Subgoal ((Hc, Ha), _)) =
          monitorHeads (cids, (Hc, Ha)) (* GEN END FUN BRANCH *)

      | (* GEN BEGIN FUN BRANCH *) monitorEvent (cids, Unify ((Hc, Ha), _, _)) =
          monitorHeads (cids, (Hc, Ha)) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) monitorEvent (cids, FailUnify ((Hc, Ha), _)) =
          monitorHeads (cids, (Hc, Ha)) (* GEN END FUN BRANCH *)

    fun (* GEN BEGIN FUN FIRST *) monitorDetail (Unify _) = !detail >= 2 (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) monitorDetail (FailUnify _) = !detail >= 2 (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) monitorDetail _ = !detail >= 1 (* GEN END FUN BRANCH *)

    (* expensive if tracing Unify! *)
    (* but: maintain only if break or trace is on *)
    (* may not be sufficient for some information *)
    fun (* GEN BEGIN FUN FIRST *) maintain (G, SolveGoal (_, _, V)) = setGoal (G, V) (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) maintain (G, RetryGoal (_, _, V)) = setGoal (G, V) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) maintain (G, FailGoal (_, _, V)) = setGoal (G, V) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) maintain (G, Unify (_, Q, P)) =
        (* show substitution for variables in clause head if tracing unification *)
        setEVarInst (Abstract.collectEVars (G, (P, I.id),
                                            Abstract.collectEVars (G, (Q, I.id), nil))) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) maintain _ = () (* GEN END FUN BRANCH *)

    fun (* GEN BEGIN FUN FIRST *) monitorBreak (None, G, e) = false (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) monitorBreak (Some (cids), G, e) =
        if monitorEvent (cids, e)
          then (maintain (G, e); traceEvent (G, e); breakAction (G); true)
        else false (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) monitorBreak (All, G, e) =
          (maintain (G, e); traceEvent (G, e); breakAction (G); true) (* GEN END FUN BRANCH *)

    fun (* GEN BEGIN FUN FIRST *) monitorTrace (None, G, e) = false (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) monitorTrace (Some (cids), G, e) =
        if monitorEvent (cids, e)
          then (maintain (G, e); traceEvent (G, e); newline (); true)
        else false (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) monitorTrace (All, G, e) =
          (maintain (G, e); traceEvent (G, e); newline (); true) (* GEN END FUN BRANCH *)

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

    fun (* GEN BEGIN FUN FIRST *) showSpec (msg, None) = print (msg ^ " = None\n") (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) showSpec (msg, Some(names)) =
        (print (msg ^ " = Some [");
         List.app ((* GEN BEGIN FUNCTION EXPRESSION *) fn name => print (" " ^ name) (* GEN END FUNCTION EXPRESSION *)) names;
         print "]\n") (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) showSpec (msg, All) = print (msg ^ " = All\n") (* GEN END FUN BRANCH *)

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

end (* GEN END FUNCTOR DECL *);  (* functor Trace *)
