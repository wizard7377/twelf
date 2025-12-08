(* Constraint Solver *)
module type CS =
sig
  (*! (CSManager : CS_MANAGER) !*)

  (* all a constraint solver must define is a module
     suitable for the constraint solver manager to install.
  *)
  let solver : CSManager.solver

end  (* module type CS *)
