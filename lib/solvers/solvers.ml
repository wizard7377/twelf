(* now in cs-manager.fun *)
(*
module CSManager = CSManager (module Global = Global
                                 (*! module IntSyn = IntSyn !*)
                                 module Unify = UnifyTrail
                                 module Fixity = Names.Fixity
                                 module ModeSyn = ModeSyn);
*)

module CSEqQ = CSEqField (module Field = Rationals
                             (*! module IntSyn = IntSyn !*)
                             module Whnf = Whnf
                             module Unify = UnifyTrail
                             (*! module CSManager = CSManager !*)
			       );

module CSIneqQ = CSIneqField (module OrderedField = Rationals
				 (*! module IntSyn = IntSyn !*)
                                  module Trail = Trail
                                  module Unify = UnifyTrail
                                  module SparseArray = SparseArray
                                  module SparseArray2 = SparseArray2
				  (*! module CSManager = CSManager !*)
                                  module CSEqField = CSEqQ
				  module Compat = Compat);

module CSEqStrings = CSEqStrings ((*! module IntSyn = IntSyn !*)
                                     module Whnf = Whnf
                                     module Unify = UnifyTrail
                                     (*! module CSManager = CSManager !*)
				       );

module CSEqBools = CSEqBools ((*! module IntSyn = IntSyn !*)
                                 module Whnf = Whnf
                                 module Unify = UnifyTrail
                                 (*! module CSManager = CSManager !*)
				   );

module CSEqZ = CSEqIntegers (module Integers = Integers
                                (*! module IntSyn = IntSyn !*)
                                module Whnf = Whnf
                                module Unify = UnifyTrail
                                (*! module CSManager = CSManager !*)
				  );

module CSIneqZ = CSIneqIntegers (module Integers = Integers
                                    module Rationals = Rationals
                                    (*! module IntSyn = IntSyn !*)
                                    module Trail = Trail
                                    module Unify = UnifyTrail
                                    module SparseArray = SparseArray
                                    module SparseArray2 = SparseArray2
                                    (*! module CSManager = CSManager !*)
                                    module CSEqIntegers = CSEqZ
				    module Compat = Compat);

module CSIntWord32 = CSIntWord ((*! module IntSyn = IntSyn !*)
                                   module Whnf = Whnf
                                   module Unify = UnifyTrail
                                   (*! module CSManager = CSManager !*)
				   let wordSize = 32);

module type CS_INSTALLER =
sig
  let version : string
end; 

(* execute for effect *)
(* wrapped in module so it can be tracked by CM *)
(CSInstaller : CS_INSTALLE)R =
struct
  let solvers = [CSEqQ.solver, CSIneqQ.solver,
		 CSEqStrings.solver,
		 CSEqBools.solver,
		 CSEqZ.solver, CSIneqZ.solver,
		 CSIntWord32.solver]
  let _ = List.app (fun s -> (CSManager.installSolver s; ())) solvers
  let version = List.foldr (fn (s, str) => #name s ^ "\n" ^ str) "" solvers
  (*
  let _ = CSManager.installSolver (CSEqQ.solver)
  let _ = CSManager.installSolver (CSIneqQ.solver)
  let _ = CSManager.installSolver (CSEqStrings.solver)
  let _ = CSManager.installSolver (CSEqBools.solver)
  let _ = CSManager.installSolver (CSEqZ.solver)
  let _ = CSManager.installSolver (CSIneqZ.solver)
  let _ = CSManager.installSolver (CSIntWord32.solver)
  let version = "12/19/2002"
  *)
end;
