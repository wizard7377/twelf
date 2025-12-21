(* now in cs-manager.fun *)

(*
structure CSManager = CSManager (structure Global = Global
                                 (*! structure IntSyn = IntSyn !*)
                                 structure Unify = UnifyTrail
                                 structure Fixity = Names.Fixity
                                 structure ModeSyn = ModeSyn);
*)

module CSEqQ =
  CSEqField
    (struct
      module Field = Rationals
    end)
    (struct
      module Whnf = Whnf
    end)
    (struct
      module Unify = UnifyTrail
    end)

module CSIneqQ =
  CSIneqField
    (struct
      module OrderedField = Rationals
    end)
    (struct
      module Trail = Trail
    end)
    (struct
      module Unify = UnifyTrail
    end)
    (struct
      module SparseArray = SparseArray
    end)
    (struct
      module SparseArray2 = SparseArray2
    end)
    (struct
      module CSEqField = CSEqQ
    end)
    (struct
      module Compat = Compat
    end)

module CSEqStrings =
  CSEqStrings
    (struct
      module Whnf = Whnf
    end)
    (struct
      module Unify = UnifyTrail
    end)

module CSEqBools =
  CSEqBools
    (struct
      module Whnf = Whnf
    end)
    (struct
      module Unify = UnifyTrail
    end)

module CSEqZ =
  CSEqIntegers
    (struct
      module Integers = Integers
    end)
    (struct
      module Whnf = Whnf
    end)
    (struct
      module Unify = UnifyTrail
    end)

module CSIneqZ =
  CSIneqIntegers
    (struct
      module Integers = Integers
    end)
    (struct
      module Rationals = Rationals
    end)
    (struct
      module Trail = Trail
    end)
    (struct
      module Unify = UnifyTrail
    end)
    (struct
      module SparseArray = SparseArray
    end)
    (struct
      module SparseArray2 = SparseArray2
    end)
    (struct
      module CSEqIntegers = CSEqZ
    end)
    (struct
      module Compat = Compat
    end)

module CSIntWord32 =
  CSIntWord
    (struct
      module Whnf = Whnf
    end)
    (struct
      module Unify = UnifyTrail
    end)

module type CS_INSTALLER = sig
  val version : string
end

(* execute for_sml effect *)

(* wrapped in structure so it can be tracked by CM *)

module CSInstaller : CS_INSTALLER = struct
  let solvers =
    [
      CSEqQ.solver;
      CSIneqQ.solver;
      CSEqStrings.solver;
      CSEqBools.solver;
      CSEqZ.solver;
      CSIneqZ.solver;
      CSIntWord32.solver;
    ]

  let _ =
    List.app
      (fun s ->
        CSManager.installSolver s;
        ())
      solvers

  let version = List.foldr (fun (s, str) -> name s ^ "\n" ^ str) "" solvers
  (*
  val _ = CSManager.installSolver (CSEqQ.solver)
  val _ = CSManager.installSolver (CSIneqQ.solver)
  val _ = CSManager.installSolver (CSEqStrings.solver)
  val _ = CSManager.installSolver (CSEqBools.solver)
  val _ = CSManager.installSolver (CSEqZ.solver)
  val _ = CSManager.installSolver (CSIneqZ.solver)
  val _ = CSManager.installSolver (CSIntWord32.solver)
  val version = "12/19/2002"
  *)
end
