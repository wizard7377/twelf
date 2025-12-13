(* now in cs-manager.fun *)
(*
structure CSManager = CSManager (structure Global = Global
                                 (*! structure IntSyn = IntSyn !*)
                                 structure Unify = UnifyTrail
                                 structure Fixity = Names.Fixity
                                 structure ModeSyn = ModeSyn);
*)

structure CSEqQ = CSEqField (structure Field = Rationals
                             (*! structure IntSyn = IntSyn !*)
                             structure Whnf = Whnf
                             structure Unify = UnifyTrail
                             (*! structure CSManager = CSManager !*)
			       );

structure CSIneqQ = CSIneqField (structure OrderedField = Rationals
				 (*! structure IntSyn = IntSyn !*)
                                  structure Trail = Trail
                                  structure Unify = UnifyTrail
                                  structure SparseArray = SparseArray
                                  structure SparseArray2 = SparseArray2
				  (*! structure CSManager = CSManager !*)
                                  structure CSEqField = CSEqQ
				  structure Compat = Compat);

structure CSEqStrings = CSEqStrings ((*! structure IntSyn = IntSyn !*)
                                     structure Whnf = Whnf
                                     structure Unify = UnifyTrail
                                     (*! structure CSManager = CSManager !*)
				       );

structure CSEqBools = CSEqBools ((*! structure IntSyn = IntSyn !*)
                                 structure Whnf = Whnf
                                 structure Unify = UnifyTrail
                                 (*! structure CSManager = CSManager !*)
				   );

structure CSEqZ = CSEqIntegers (structure Integers = Integers
                                (*! structure IntSyn = IntSyn !*)
                                structure Whnf = Whnf
                                structure Unify = UnifyTrail
                                (*! structure CSManager = CSManager !*)
				  );

structure CSIneqZ = CSIneqIntegers (structure Integers = Integers
                                    structure Rationals = Rationals
                                    (*! structure IntSyn = IntSyn !*)
                                    structure Trail = Trail
                                    structure Unify = UnifyTrail
                                    structure SparseArray = SparseArray
                                    structure SparseArray2 = SparseArray2
                                    (*! structure CSManager = CSManager !*)
                                    structure CSEqIntegers = CSEqZ
				    structure Compat = Compat);

structure CSIntWord32 = CSIntWord ((*! structure IntSyn = IntSyn !*)
                                   structure Whnf = Whnf
                                   structure Unify = UnifyTrail
                                   (*! structure CSManager = CSManager !*)
				   (* GEN BEGIN TAG OUTSIDE LET *) val wordSize = 32 (* GEN END TAG OUTSIDE LET *));

(* GEN BEGIN SIGNATURE DECLARATION *) signature CS_INSTALLER =
sig
  val version : string
end (* GEN END SIGNATURE DECLARATION *); 

(* execute for effect *)
(* wrapped in structure so it can be tracked by CM *)
structure CSInstaller : CS_INSTALLER =
struct
  (* GEN BEGIN TAG OUTSIDE LET *) val solvers = [CSEqQ.solver, CSIneqQ.solver,
  		 CSEqStrings.solver,
  		 CSEqBools.solver,
  		 CSEqZ.solver, CSIneqZ.solver,
  		 CSIntWord32.solver] (* GEN END TAG OUTSIDE LET *)
  (* GEN BEGIN TAG OUTSIDE LET *) val _ = List.app ((* GEN BEGIN FUNCTION EXPRESSION *) fn s => (CSManager.installSolver s; ()) (* GEN END FUNCTION EXPRESSION *)) solvers (* GEN END TAG OUTSIDE LET *)
  (* GEN BEGIN TAG OUTSIDE LET *) val version = List.foldr ((* GEN BEGIN FUNCTION EXPRESSION *) fn (s, str) => #name s ^ "\n" ^ str (* GEN END FUNCTION EXPRESSION *)) "" solvers (* GEN END TAG OUTSIDE LET *)
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
end;
