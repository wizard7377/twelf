(* Constraint Solver Manager *)
(* Author: Roberto Virga *)

(* GEN BEGIN SIGNATURE DECLARATION *) signature CS_MANAGER =
sig
  (* structure IntSyn : INTSYN *)
  structure Fixity  : FIXITY
  (*! structure ModeSyn : MODESYN !*)

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

  (* solver handling functions *)
  val setInstallFN : (sig_entry -> IntSyn.cid) -> unit

  val installSolver : solver -> IntSyn.csid
  val resetSolvers  : unit -> unit
  val useSolver     : string -> unit

  (* parsing foreign constatnts *)
  val parse : string -> (IntSyn.csid * IntSyn.con_dec) option

  (* trailing operations *)
  val reset : unit -> unit
  val trail  : (unit -> 'a) -> 'a

end (* GEN END SIGNATURE DECLARATION *)  (* signature CS_MANAGER *)