(* Elaboration for module expressions *)
(* Author: Kevin Watkins *)

module ReconModule
  (Global : GLOBAL)
   (*! (IntSyn : INTSYN) !*)
   (Names : NAMES)
   (*! sharing Names.IntSyn = IntSyn !*)
   (*! module Paths' : PATHS !*)
   module ReconTerm' : RECON_TERM
   (*! sharing ReconTerm'.IntSyn = IntSyn !*)
   (*! sharing ReconTerm'.Paths = Paths' !*)
   module ModSyn' : MODSYN
   (*! sharing ModSyn'.IntSyn = IntSyn !*)
     sharing ModSyn'.Names = Names
   (IntTree : TABLE with type key = int))
  : RECON_MODULE =
struct

  module ExtSyn = ReconTerm'
  (*! module Paths = Paths' !*)
  module ModSyn = ModSyn'

  exception Error of string

  let rec error (r, msg) = raise Error (Paths.wrap (r, msg))

  type strexp = unit -> IntSyn.mid * Paths.region

  let rec strexp (ids, id, r) () =
      let
        let qid = Names.Qid (ids, id)
      in
        case Names.structLookup qid
          of NONE => error (r, "Undeclared module " ^
                            Names.qidToString (valOf (Names.structUndef qid)))
           | SOME mid => (mid, r)
      end

  let rec strexpToStrexp (f:strexp) = #1 (f ())

  type inst =
      External of ExtSyn.term
    | Internal of IntSyn.cid

  type eqn = IntSyn.cid * Inst * Paths.region

  type inst = Names.namespace * eqn list -> eqn list

  let rec coninst ((ids, id, r1), tm, r2) (ns, eqns) =
      let
        let qid = Names.Qid (ids, id)
      in
        case Names.constLookupIn (ns, qid)
          of NONE => error (r1, "Undeclared identifier "
                            ^ Names.qidToString (valOf (Names.constUndefIn (ns, qid))))
           | SOME cid => (cid, External tm (* this is wrong because constants in the sig being instantiated might incorrectly appear in tm -kw *), r2)::eqns
      end

  let rec addStructEqn (rEqns, r1, r2, ids, mid1, mid2) =
      let
        let ns1 = Names.getComponents mid1
        let ns2 = Names.getComponents mid2
        let rec push eqn = rEqns := eqn::(!rEqns)

        let rec doConst (name, cid1) =
            case Names.constLookupIn (ns2, Names.Qid (nil, name))
              of NONE => error (r1, "Instantiating module lacks component " ^
                                Names.qidToString (Names.Qid (rev ids, name)))
               | SOME cid2 => push (cid1, Internal cid2, r2)

        let rec doStruct (name, mid1) =
            case Names.structLookupIn (ns2, Names.Qid (nil, name))
              of NONE => error (r1, "Instantiating module lacks component " ^
                                Names.qidToString (Names.Qid (rev ids, name)))
               | SOME mid2 => addStructEqn (rEqns, r1, r2, name::ids, mid1, mid2)
      in
        Names.appConsts doConst ns1;
        Names.appStructs doStruct ns1
      end

  let rec strinst ((ids, id, r1), strexp, r3) (ns, eqns) =
      let
        let qid = Names.Qid (ids, id)
        let mid1 = (case Names.structLookupIn (ns, qid)
                      of NONE => error (r1, "Undeclared module "
                                        ^ Names.qidToString (valOf (Names.structUndefIn (ns, qid))))
                       | SOME mid1 => mid1)

        let (mid2, r2) = strexp ()
        let rEqns = ref eqns
      in
        addStructEqn (rEqns, r2, r3, nil, mid1, mid2);
        !rEqns
      end

  type whereclause = Names.namespace -> eqn list
  type sigexp = ModSyn.module option -> ModSyn.module * whereclause list

  let rec thesig (SOME module) = (module, nil)

  let rec sigid (id, r) NONE =
      (case ModSyn.lookupSigDef id
         of NONE => error (r, "Undefined module type " ^ id)
          | SOME module => (module, nil))

  let rec wheresig (sigexp, instList) moduleOpt =
      let
        let (module, wherecls) = sigexp moduleOpt
        let rec wherecl ns = foldr (fn (inst, eqns) => inst (ns, eqns)) nil instList
      in
        (module, wherecls @ [wherecl])
      end

  let rec sigexpToSigexp (sigexp, moduleOpt) = sigexp moduleOpt

  type sigdef = ModSyn.module option -> string option * ModSyn.module * whereclause list

  let rec sigdef (idOpt, sigexp) moduleOpt =
      let
        let (module, wherecls) = sigexp moduleOpt
      in
        (idOpt, module, wherecls)
      end

  let rec sigdefToSigdef (sigdef, moduleOpt) = sigdef moduleOpt

  type structDec =
      StructDec of string option * ModSyn.module * whereclause list
    | StructDef of string option * IntSyn.mid

  type structdec = ModSyn.module option -> StructDec

  let rec structdec (idOpt, sigexp) moduleOpt =
      let
        let (module, inst) = sigexp moduleOpt
      in
        StructDec (idOpt, module, inst)
      end

  let rec structdef (idOpt, strexp) NONE =
      let
        let mid = strexpToStrexp strexp
      in
        StructDef (idOpt, mid)
      end

  let rec structdecToStructDec (structdec, moduleOpt) = structdec moduleOpt

  type eqnTable = (Inst * Paths.region) list ref IntTree.Table

  let rec applyEqns wherecl namespace =
      let
        let eqns = wherecl namespace

        let table : eqnTable = IntTree.new (0)
        let rec add (cid, Inst, r) =
            (case IntTree.lookup table cid
               of NONE => IntTree.insert table (cid, ref [(Inst, r)])
                | SOME rl => rl := (Inst, r)::(!rl))
        let _ = List.app add eqns

        let rec doInst = function ((Internal cid, r), condec) -> 
              (ModSyn.strictify (ExtSyn.internalInst (condec, ModSyn.abbrevify (cid, IntSyn.sgnLookup cid), r))
              handle ExtSyn.Error msg =>
                raise ExtSyn.Error (msg ^ "\nin instantiation generated for "
                                    ^ Names.qidToString (Names.constQid cid)))
          | ((External tm, r), condec) -> 
              ModSyn.strictify (ExtSyn.externalInst (condec, tm, r))

        let rec transformConDec (cid, condec) =
            (case IntTree.lookup table cid
               of NONE => condec
                | SOME (ref l) => List.foldr doInst condec l)
      in
        transformConDec
      end

  let rec moduleWhere (module, wherecl) =
      let
        let (mark, markStruct) = IntSyn.sgnSize ()
        let module' = ModSyn.instantiateModule (module, applyEqns wherecl)
        let _ = Names.resetFrom (mark, markStruct)
        (* let _ = IntSyn.resetFrom (mark, markStruct) *)
      in
        module'
      end

end
