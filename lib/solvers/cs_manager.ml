(* Constraint Solver Manager *)
(* Author: Roberto Virga *)

functor (* GEN BEGIN FUNCTOR DECL *) CSManager (structure Global : GLOBAL
                   (*! structure IntSyn : INTSYN !*)
                   structure Unify : UNIFY
                   (*! sharing Unify.IntSyn = IntSyn !*)
                   structure Fixity : FIXITY
                   (*! structure ModeSyn : MODESYN !*))
  : CS_MANAGER =
struct
  structure IntSyn  = IntSyn
  structure Fixity  = Fixity
  (* structure ModeSyn = ModeSyn *)

  type sig_entry = (* global signature entry *)
    (* constant declaration plus optional precedence and mode information *)
    IntSyn.con_dec * Fixity.fixity option * ModeSyn.mode_spine list

  type fgn_con_dec = (* foreign constant declaration *)
    {
      parse : string -> IntSyn.con_dec option
    }

  type solver = (* constraint solver *)
    {
      (* name is the name of the solver *)
      name : string,
      (* keywords identifying the type of solver *)
      (* NOTE: no two solvers with the same keywords may be active simultaneously *)
      keywords : string,
      (* names of other constraint solvers needed *)
      needs : string list,
      (* foreign constants declared (if any) *)
      fgnConst : fgn_con_dec option,
      (* install constants *)
      init : (int * (sig_entry -> IntSyn.cid)) -> unit,
      (* reset internal status *)
      reset : unit -> unit,
      (* trailing operations *)
      mark : unit -> unit,
      unwind : unit -> unit
    }

  exception Error of string

  local

    (* vacuous solver *)
    (* GEN BEGIN TAG OUTSIDE LET *) val emptySolver =
        {
          name = "",
          keywords = "",
          needs = nil,
    
          fgnConst = NONE,
    
          init = ((* GEN BEGIN FUNCTION EXPRESSION *) fn _ => () (* GEN END FUNCTION EXPRESSION *)),
    
          reset = ((* GEN BEGIN FUNCTION EXPRESSION *) fn () => () (* GEN END FUNCTION EXPRESSION *)),
          mark = ((* GEN BEGIN FUNCTION EXPRESSION *) fn () => () (* GEN END FUNCTION EXPRESSION *)),
          unwind = ((* GEN BEGIN FUNCTION EXPRESSION *) fn () => () (* GEN END FUNCTION EXPRESSION *))
        } (* GEN END TAG OUTSIDE LET *)

    (* Twelf unification as a constraint solver *)
    (* GEN BEGIN TAG OUTSIDE LET *) val unifySolver =
        {
          name = "Unify",
          keywords = "unification",
          needs = nil,
    
          fgnConst = NONE,
    
          init = ((* GEN BEGIN FUNCTION EXPRESSION *) fn _ => () (* GEN END FUNCTION EXPRESSION *)),
    
          reset  = Unify.reset,
          mark   = Unify.mark,
          unwind = Unify.unwind
        } (* GEN END TAG OUTSIDE LET *)

    (* List of installed solvers *)

    datatype solver = Solver of solver * bool ref

    (* GEN BEGIN TAG OUTSIDE LET *) val maxCS = Global.maxCSid (* GEN END TAG OUTSIDE LET *)
    (* GEN BEGIN TAG OUTSIDE LET *) val csArray = Array.array (maxCS+1, Solver (emptySolver, ref false)) : solver Array.array (* GEN END TAG OUTSIDE LET *)
    (* GEN BEGIN TAG OUTSIDE LET *) val _ = Array.update (csArray, 0, Solver (unifySolver, ref true)) (* GEN END TAG OUTSIDE LET *)
    (* GEN BEGIN TAG OUTSIDE LET *) val nextCS = ref(1) : int ref (* GEN END TAG OUTSIDE LET *)

    (* Installing function *)
    (* GEN BEGIN TAG OUTSIDE LET *) val installFN = ref ((* GEN BEGIN FUNCTION EXPRESSION *) fn _ => ~1 (* GEN END FUNCTION EXPRESSION *)) : (sig_entry -> IntSyn.cid) ref (* GEN END TAG OUTSIDE LET *)
    fun setInstallFN f = (installFN := f)

    (* install the specified solver *)
    fun installSolver (solver) =
          let
            (* val _ = print ("Installing constraint domain " ^ #name solver ^ "\n") *)
            (* GEN BEGIN TAG OUTSIDE LET *) val cs = !nextCS (* GEN END TAG OUTSIDE LET *)
            (* GEN BEGIN TAG OUTSIDE LET *) val _ = if !nextCS > maxCS
                    then raise Error "too many constraint solvers"
                    else () (* GEN END TAG OUTSIDE LET *)
            (* GEN BEGIN TAG OUTSIDE LET *) val _ = Array.update (csArray, cs, Solver (solver, ref false)) (* GEN END TAG OUTSIDE LET *);
            (* GEN BEGIN TAG OUTSIDE LET *) val _ = nextCS := !nextCS+1 (* GEN END TAG OUTSIDE LET *)
          in
            cs
          end

    (* install the unification solver *)
    (* GEN BEGIN TAG OUTSIDE LET *) val _ = installSolver (unifySolver) (* GEN END TAG OUTSIDE LET *)

    (* GEN BEGIN TAG OUTSIDE LET *) val activeKeywords = ref nil : string list ref (* GEN END TAG OUTSIDE LET *)

    (* make all the solvers inactive *)
    fun resetSolvers () =
          (
            ArraySlice.appi ((* GEN BEGIN FUNCTION EXPRESSION *) fn (cs, Solver (solver, active)) =>
                                if !active then
                                    (
                                     active := false;
                                     #reset(solver) ()
                                    )
                                else () (* GEN END FUNCTION EXPRESSION *))
                            (ArraySlice.slice (csArray, 0, SOME(!nextCS)));
            activeKeywords := nil;
            useSolver "Unify"
          )

    (* make the specified solver active *)
    and useSolver name =
          let
            exception Found of IntSyn.csid
            fun findSolver name =
                  (
                    ArraySlice.appi ((* GEN BEGIN FUNCTION EXPRESSION *) fn (cs, Solver (solver, _)) =>
                                        if (#name(solver) = name)
                                        then raise Found cs
                                        else () (* GEN END FUNCTION EXPRESSION *))
                                    (ArraySlice.slice (csArray, 0, SOME(!nextCS)));
                    NONE
                  ) handle Found cs => SOME(cs)
          in
            case findSolver name
              of SOME(cs) =>
                   let
                     (* GEN BEGIN TAG OUTSIDE LET *) val Solver (solver, active) = Array.sub (csArray, cs) (* GEN END TAG OUTSIDE LET *)
                   in
                     if !active then ()
                     else if List.exists ((* GEN BEGIN FUNCTION EXPRESSION *) fn s => s = #keywords(solver) (* GEN END FUNCTION EXPRESSION *))
                                         (!activeKeywords)
                     then raise Error ("solver " ^ name ^
                                       " is incompatible with a currently active solver")
                     else
                       (
                          active := true;
                          activeKeywords := #keywords(solver) :: (!activeKeywords);
                          List.app useSolver (#needs(solver));
                          #init(solver) (cs, !installFN)
                       )
                   end
               | NONE => raise Error ("solver " ^ name ^ " not found")
          end

  (* ask each active solver to try and parse the given string *)
  fun parse string =
        let
          exception Parsed of IntSyn.csid * IntSyn.con_dec
          fun parse' (cs, solver : solver) =
                (case #fgnConst(solver)
                           of NONE => ()
                            | SOME(fgnConDec) =>
                                (case #parse(fgnConDec) (string)
                                   of NONE => ()
                                    | SOME conDec => raise Parsed (cs, conDec)))
        in
          (
            ArraySlice.appi ((* GEN BEGIN FUNCTION EXPRESSION *) fn (cs, Solver (solver, active)) =>
                                if !active then parse' (cs, solver) else () (* GEN END FUNCTION EXPRESSION *))
                            (ArraySlice.slice (csArray, 0, SOME(!nextCS)));
            NONE
          ) handle Parsed info => SOME(info)
        end


  (* GEN BEGIN TAG OUTSIDE LET *) val markCount = ref 0 : int ref (* GEN END TAG OUTSIDE LET *)

  (* reset the internal status of all the active solvers *)
  fun reset () =
        ArraySlice.appi ((* GEN BEGIN FUNCTION EXPRESSION *) fn (_, Solver (solver, active)) =>
                            if !active then (markCount := 0; #reset(solver) ())
                            else () (* GEN END FUNCTION EXPRESSION *))
                        (ArraySlice.slice (csArray, 0, SOME(!nextCS)));


  (* mark all active solvers *)
  fun mark () =
        (markCount := !markCount + 1;
          ArraySlice.appi ((* GEN BEGIN FUNCTION EXPRESSION *) fn (_, Solver (solver, active)) =>
                              if !active then #mark(solver) () else () (* GEN END FUNCTION EXPRESSION *))
                          (ArraySlice.slice (csArray, 0, SOME(!nextCS))))

  (* unwind all active solvers *)
  fun unwind targetCount =
    let
      fun (* GEN BEGIN FUN FIRST *) unwind' 0 = (markCount := targetCount) (* GEN END FUN FIRST *)
        | (* GEN BEGIN FUN BRANCH *) unwind' k =
          (ArraySlice.appi ((* GEN BEGIN FUNCTION EXPRESSION *) fn (_, Solver (solver, active)) =>
                               if !active then #unwind(solver) () else () (* GEN END FUNCTION EXPRESSION *))
           (ArraySlice.slice (csArray, 0, SOME(!nextCS)));
           unwind' (k-1)) (* GEN END FUN BRANCH *)
    in
      unwind' (!markCount - targetCount)
    end


  (* trail the give function *)
  fun trail f =
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val current = !markCount (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val _ = mark () (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val r = f() (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val _ = unwind current (* GEN END TAG OUTSIDE LET *)
        in
          r
        end
  in
    (* GEN BEGIN TAG OUTSIDE LET *) val setInstallFN = setInstallFN (* GEN END TAG OUTSIDE LET *)

    (* GEN BEGIN TAG OUTSIDE LET *) val installSolver = installSolver (* GEN END TAG OUTSIDE LET *)
    (* GEN BEGIN TAG OUTSIDE LET *) val resetSolvers = resetSolvers (* GEN END TAG OUTSIDE LET *)
    (* GEN BEGIN TAG OUTSIDE LET *) val useSolver = useSolver (* GEN END TAG OUTSIDE LET *)

    (* GEN BEGIN TAG OUTSIDE LET *) val parse = parse (* GEN END TAG OUTSIDE LET *)

    (* GEN BEGIN TAG OUTSIDE LET *) val reset = reset (* GEN END TAG OUTSIDE LET *)
    (* GEN BEGIN TAG OUTSIDE LET *) val trail = trail (* GEN END TAG OUTSIDE LET *)
  end
end (* GEN END FUNCTOR DECL *)  (* functor CSManager *)

structure CSManager = CSManager (structure Global = Global
                                 (*! structure IntSyn = IntSyn !*)
                                 structure Unify = UnifyTrail
                                 structure Fixity = Names.Fixity
                                 (*! structure ModeSyn = ModeSyn !*));
