(* Elaboration for module expressions *)
(* Author: Kevin Watkins *)

functor (* GEN BEGIN FUNCTOR DECL *) ReconModule
  (structure Global : GLOBAL
   (*! structure IntSyn : INTSYN !*)
   structure Names : NAMES
   (*! sharing Names.IntSyn = IntSyn !*)
   (*! structure Paths' : PATHS !*)
   structure ReconTerm' : RECON_TERM
   (*! sharing ReconTerm'.IntSyn = IntSyn !*)
   (*! sharing ReconTerm'.Paths = Paths' !*)
   structure ModSyn' : MODSYN
   (*! sharing ModSyn'.IntSyn = IntSyn !*)
     sharing ModSyn'.Names = Names
   structure IntTree : TABLE where type key = int)
  : RECON_MODULE =
struct

  structure ExtSyn = ReconTerm'
  (*! structure Paths = Paths' !*)
  structure ModSyn = ModSyn'

  exception Error of string

  fun error (r, msg) = raise Error (Paths.wrap (r, msg))

  type strexp = unit -> IntSyn.mid * Paths.region

  fun strexp (ids, id, r) () =
      let
        (* GEN BEGIN TAG OUTSIDE LET *) val qid = Names.Qid (ids, id) (* GEN END TAG OUTSIDE LET *)
      in
        case Names.structLookup qid
          of NONE => error (r, "Undeclared structure " ^
                            Names.qidToString (valOf (Names.structUndef qid)))
           | SOME mid => (mid, r)
      end

  fun strexpToStrexp (f:strexp) = #1 (f ())

  datatype inst =
      External of ExtSyn.term
    | Internal of IntSyn.cid

  type eqn = IntSyn.cid * inst * Paths.region

  type inst = Names.namespace * eqn list -> eqn list

  fun coninst ((ids, id, r1), tm, r2) (ns, eqns) =
      let
        (* GEN BEGIN TAG OUTSIDE LET *) val qid = Names.Qid (ids, id) (* GEN END TAG OUTSIDE LET *)
      in
        case Names.constLookupIn (ns, qid)
          of NONE => error (r1, "Undeclared identifier "
                            ^ Names.qidToString (valOf (Names.constUndefIn (ns, qid))))
           | SOME cid => (cid, External tm (* this is wrong because constants in the sig being instantiated might incorrectly appear in tm -kw *), r2)::eqns
      end

  fun addStructEqn (rEqns, r1, r2, ids, mid1, mid2) =
      let
        (* GEN BEGIN TAG OUTSIDE LET *) val ns1 = Names.getComponents mid1 (* GEN END TAG OUTSIDE LET *)
        (* GEN BEGIN TAG OUTSIDE LET *) val ns2 = Names.getComponents mid2 (* GEN END TAG OUTSIDE LET *)
        fun push eqn = rEqns := eqn::(!rEqns)
  
        fun doConst (name, cid1) =
            case Names.constLookupIn (ns2, Names.Qid (nil, name))
              of NONE => error (r1, "Instantiating structure lacks component " ^
                                Names.qidToString (Names.Qid (rev ids, name)))
               | SOME cid2 => push (cid1, Internal cid2, r2)
  
        fun doStruct (name, mid1) =
            case Names.structLookupIn (ns2, Names.Qid (nil, name))
              of NONE => error (r1, "Instantiating structure lacks component " ^
                                Names.qidToString (Names.Qid (rev ids, name)))
               | SOME mid2 => addStructEqn (rEqns, r1, r2, name::ids, mid1, mid2)
      in
        Names.appConsts doConst ns1;
        Names.appStructs doStruct ns1
      end

  fun strinst ((ids, id, r1), strexp, r3) (ns, eqns) =
      let
        (* GEN BEGIN TAG OUTSIDE LET *) val qid = Names.Qid (ids, id) (* GEN END TAG OUTSIDE LET *)
        (* GEN BEGIN TAG OUTSIDE LET *) val mid1 = (case Names.structLookupIn (ns, qid)
                      of NONE => error (r1, "Undeclared structure "
                                        ^ Names.qidToString (valOf (Names.structUndefIn (ns, qid))))
                       | SOME mid1 => mid1) (* GEN END TAG OUTSIDE LET *)
  
        (* GEN BEGIN TAG OUTSIDE LET *) val (mid2, r2) = strexp () (* GEN END TAG OUTSIDE LET *)
        (* GEN BEGIN TAG OUTSIDE LET *) val rEqns = ref eqns (* GEN END TAG OUTSIDE LET *)
      in
        addStructEqn (rEqns, r2, r3, nil, mid1, mid2);
        !rEqns
      end

  type whereclause = Names.namespace -> eqn list
  type sigexp = ModSyn.module option -> ModSyn.module * whereclause list

  fun thesig (SOME module) = (module, nil)

  fun sigid (id, r) NONE =
      (case ModSyn.lookupSigDef id
         of NONE => error (r, "Undefined signature " ^ id)
          | SOME module => (module, nil))

  fun wheresig (sigexp, instList) moduleOpt =
      let
        (* GEN BEGIN TAG OUTSIDE LET *) val (module, wherecls) = sigexp moduleOpt (* GEN END TAG OUTSIDE LET *)
        fun wherecl ns = foldr ((* GEN BEGIN FUNCTION EXPRESSION *) fn (inst, eqns) => inst (ns, eqns) (* GEN END FUNCTION EXPRESSION *)) nil instList
      in
        (module, wherecls @ [wherecl])
      end

  fun sigexpToSigexp (sigexp, moduleOpt) = sigexp moduleOpt

  type sigdef = ModSyn.module option -> string option * ModSyn.module * whereclause list

  fun sigdef (idOpt, sigexp) moduleOpt =
      let
        (* GEN BEGIN TAG OUTSIDE LET *) val (module, wherecls) = sigexp moduleOpt (* GEN END TAG OUTSIDE LET *)
      in
        (idOpt, module, wherecls)
      end

  fun sigdefToSigdef (sigdef, moduleOpt) = sigdef moduleOpt

  datatype struct_dec =
      StructDec of string option * ModSyn.module * whereclause list
    | StructDef of string option * IntSyn.mid

  type structdec = ModSyn.module option -> struct_dec

  fun structdec (idOpt, sigexp) moduleOpt =
      let
        (* GEN BEGIN TAG OUTSIDE LET *) val (module, inst) = sigexp moduleOpt (* GEN END TAG OUTSIDE LET *)
      in
        StructDec (idOpt, module, inst)
      end

  fun structdef (idOpt, strexp) NONE =
      let
        (* GEN BEGIN TAG OUTSIDE LET *) val mid = strexpToStrexp strexp (* GEN END TAG OUTSIDE LET *)
      in
        StructDef (idOpt, mid)
      end

  fun structdecToStructDec (structdec, moduleOpt) = structdec moduleOpt

  type eqn_table = (inst * Paths.region) list ref IntTree.table

  fun applyEqns wherecl namespace =
      let
        (* GEN BEGIN TAG OUTSIDE LET *) val eqns = wherecl namespace (* GEN END TAG OUTSIDE LET *)
  
        (* GEN BEGIN TAG OUTSIDE LET *) val table : eqn_table = IntTree.new (0) (* GEN END TAG OUTSIDE LET *)
        fun add (cid, Inst, r) =
            (case IntTree.lookup table cid
               of NONE => IntTree.insert table (cid, ref [(Inst, r)])
                | SOME rl => rl := (Inst, r)::(!rl))
        (* GEN BEGIN TAG OUTSIDE LET *) val _ = List.app add eqns (* GEN END TAG OUTSIDE LET *)
  
        fun (* GEN BEGIN FUN FIRST *) doInst ((Internal cid, r), condec) =
              (ModSyn.strictify (ExtSyn.internalInst (condec, ModSyn.abbrevify (cid, IntSyn.sgnLookup cid), r))
              handle ExtSyn.Error msg =>
                raise ExtSyn.Error (msg ^ "\nin instantiation generated for "
                                    ^ Names.qidToString (Names.constQid cid))) (* GEN END FUN FIRST *)
          | (* GEN BEGIN FUN BRANCH *) doInst ((External tm, r), condec) =
              ModSyn.strictify (ExtSyn.externalInst (condec, tm, r)) (* GEN END FUN BRANCH *)
  
        fun transformConDec (cid, condec) =
            (case IntTree.lookup table cid
               of NONE => condec
                | SOME (ref l) => List.foldr doInst condec l)
      in
        transformConDec
      end

  fun moduleWhere (module, wherecl) =
      let
        (* GEN BEGIN TAG OUTSIDE LET *) val (mark, markStruct) = IntSyn.sgnSize () (* GEN END TAG OUTSIDE LET *)
        (* GEN BEGIN TAG OUTSIDE LET *) val module' = ModSyn.instantiateModule (module, applyEqns wherecl) (* GEN END TAG OUTSIDE LET *)
        (* GEN BEGIN TAG OUTSIDE LET *) val _ = Names.resetFrom (mark, markStruct) (* GEN END TAG OUTSIDE LET *)
        (* val _ = IntSyn.resetFrom (mark, markStruct) *)
      in
        module'
      end

end (* GEN END FUNCTOR DECL *)
