open Basis
(* now in cs-manager.fun *)

(*
structure Cs.CSManager = Cs.CSManager (structure Global = Global
                                 (*! structure IntSyn = IntSyn !*)
                                 structure Unify = UnifyTrail
                                 structure Fixity = Names.Fixity
                                 structure ModeSyn = ModeSyn);
*)

module CSEqQ =
  Cs.CSEqField
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
  Cs.CSIneqField
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
      module CSEqField = Cs.CSEqQ
    end)
    (struct
      module Compat = Compat
    end)

module CSEqStrings =
  Cs.CSEqStrings
    (struct
      module Whnf = Whnf
    end)
    (struct
      module Unify = UnifyTrail
    end)

module CSEqBools =
  Cs.CSEqBools
    (struct
      module Whnf = Whnf
    end)
    (struct
      module Unify = UnifyTrail
    end)

module CSEqZ =
  Cs.CSEqIntegers
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
  Cs.CSIneqIntegers
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
      module CSEqIntegers = Cs.CSEqZ
    end)
    (struct
      module Compat = Compat
    end)

module CSIntWord32 =
  Cs.CSIntWord
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

module CSInstaller : Cs.CS_INSTALLER = struct
  let solvers =
    [
      Cs.CSEqQ.solver;
      Cs.CSIneqQ.solver;
      Cs.CSEqStrings.solver;
      Cs.CSEqBools.solver;
      Cs.CSEqZ.solver;
      Cs.CSIneqZ.solver;
      Cs.CSIntWord32.solver;
    ]

  let _ =
    List.app
      (fun s ->
        Cs.CSManager.installSolver s;
        ())
      solvers

  let version = List.foldr (fun (s, str) -> name s ^ "\n" ^ str) "" solvers
  (*
  val _ = Cs.CSManager.installSolver (Cs.CSEqQ.solver)
  val _ = Cs.CSManager.installSolver (Cs.CSIneqQ.solver)
  val _ = Cs.CSManager.installSolver (Cs.CSEqStrings.solver)
  val _ = Cs.CSManager.installSolver (Cs.CSEqBools.solver)
  val _ = Cs.CSManager.installSolver (Cs.CSEqZ.solver)
  val _ = Cs.CSManager.installSolver (Cs.CSIneqZ.solver)
  val _ = Cs.CSManager.installSolver (Cs.CSIntWord32.solver)
  val version = "12/19/2002"
  *)
end
