(* External syntax for_sml module expressions *)

(* Author: Kevin Watkins *)

module type MODEXTSYN = sig
  module ExtSyn : Recon_term.EXTSYN

  (*! structure Paths : Paths.PATHS !*)
  type strexp

  val strexp : string list * string * Paths.region -> strexp

  type inst

  val coninst :
    (string list * string * Paths.region) * ExtSyn.term * Paths.region -> inst

  val strinst :
    (string list * string * Paths.region) * strexp * Paths.region -> inst

  type sigexp

  val thesig : sigexp
  val sigid : string * Paths.region -> sigexp
  val wheresig : sigexp * inst list -> sigexp

  type sigdef

  val sigdef : string option * sigexp -> sigdef

  type structdec

  val structdec : string option * sigexp -> structdec
  val structdef : string option * strexp -> structdec
end

module type RECON_MODULE = sig
  include MODEXTSYN
  module ModSyn : Modsyn.MODSYN

  exception Error of string

  type whereclause

  type structDec =
    | StructDec of string option * ModSyn.module_ * whereclause list
    | StructDef of string option * IntSyn.mid

  val strexpToStrexp : strexp -> IntSyn.mid

  val sigexpToSigexp :
    sigexp * ModSyn.module_ option -> ModSyn.module_ * whereclause list

  val sigdefToSigdef :
    sigdef * ModSyn.module_ option ->
    string option * ModSyn.module_ * whereclause list

  val structdecToStructDec : structdec * ModSyn.module_ option -> structDec
  val moduleWhere : ModSyn.module_ * whereclause -> ModSyn.module_
end
(* Elaboration for_sml module expressions *)

(* Author: Kevin Watkins *)

module ReconModule
    (Global : Global.GLOBAL)
    (Names : Names.NAMES)
    (ReconTerm' : Recon_term.RECON_TERM)
    (ModSyn' : Modsyn.MODSYN) : RECON_MODULE = struct
  module ExtSyn = ReconTerm'
  (*! structure Paths = Paths' !*)

  module ModSyn = ModSyn'

  exception Error of string

  let rec error (r, msg) = raise (Error (Paths.wrap (r, msg)))

  type strexp = unit -> IntSyn.mid * Paths.region

  let rec strexp (ids, id, r) () =
    let qid = Names.Qid (ids, id) in
    match Names.structLookup qid with
    | None ->
        error
          ( r,
            "Undeclared structure "
            ^ Names.qidToString (valOf (Names.structUndef qid)) )
    | Some mid -> (mid, r)

  let rec strexpToStrexp (f : strexp) = 1 (f ())

  type inst = External of ExtSyn.term | Internal of IntSyn.cid
  type eqn = IntSyn.cid * inst * Paths.region
  type inst = Names.namespace * eqn list -> eqn list

  let rec coninst ((ids, id, r1), tm, r2) (ns, eqns) =
    let qid = Names.Qid (ids, id) in
    match Names.constLookupIn (ns, qid) with
    | None ->
        error
          ( r1,
            "Undeclared identifier "
            ^ Names.qidToString (valOf (Names.constUndefIn (ns, qid))) )
    | Some cid ->
        ( cid,
          External tm
          (* this is wrong because constants in the sig being instantiated might incorrectly appear in tm -kw *),
          r2 )
        :: eqns

  let rec addStructEqn (rEqns, r1, r2, ids, mid1, mid2) =
    let ns1 = Names.getComponents mid1 in
    let ns2 = Names.getComponents mid2 in
    let rec push eqn = rEqns := eqn :: !rEqns in
    let rec doConst (name, cid1) =
      match Names.constLookupIn (ns2, Names.Qid ([], name)) with
      | None ->
          error
            ( r1,
              "Instantiating structure lacks component "
              ^ Names.qidToString (Names.Qid (rev ids, name)) )
      | Some cid2 -> push (cid1, Internal cid2, r2)
    in
    let rec doStruct (name, mid1) =
      match Names.structLookupIn (ns2, Names.Qid ([], name)) with
      | None ->
          error
            ( r1,
              "Instantiating structure lacks component "
              ^ Names.qidToString (Names.Qid (rev ids, name)) )
      | Some mid2 -> addStructEqn (rEqns, r1, r2, name :: ids, mid1, mid2)
    in
    Names.appConsts doConst ns1;
    Names.appStructs doStruct ns1

  let rec strinst ((ids, id, r1), strexp, r3) (ns, eqns) =
    let qid = Names.Qid (ids, id) in
    let mid1 =
      match Names.structLookupIn (ns, qid) with
      | None ->
          error
            ( r1,
              "Undeclared structure "
              ^ Names.qidToString (valOf (Names.structUndefIn (ns, qid))) )
      | Some mid1 -> mid1
    in
    let mid2, r2 = strexp () in
    let rEqns = ref eqns in
    addStructEqn (rEqns, r2, r3, [], mid1, mid2);
    !rEqns

  type whereclause = Names.namespace -> eqn list
  type sigexp = ModSyn.module_ option -> ModSyn.module_ * whereclause list

  let rec thesig (Some module_) = (module_, [])

  let rec sigid (id, r) None =
    match ModSyn.lookupSigDef id with
    | None -> error (r, "Undefined signature " ^ id)
    | Some module_ -> (module_, [])

  let rec wheresig (sigexp, instList) moduleOpt =
    let module_, wherecls = sigexp moduleOpt in
    let rec wherecl ns =
      foldr (fun (inst, eqns) -> inst (ns, eqns)) [] instList
    in
    (module_, wherecls @ [ wherecl ])

  let rec sigexpToSigexp (sigexp, moduleOpt) = sigexp moduleOpt

  type sigdef =
    ModSyn.module_ option -> string option * ModSyn.module_ * whereclause list

  let rec sigdef (idOpt, sigexp) moduleOpt =
    let module_, wherecls = sigexp moduleOpt in
    (idOpt, module_, wherecls)

  let rec sigdefToSigdef (sigdef, moduleOpt) = sigdef moduleOpt

  type structDec =
    | StructDec of string option * ModSyn.module_ * whereclause list
    | StructDef of string option * IntSyn.mid

  type structdec = ModSyn.module_ option -> structDec

  let rec structdec (idOpt, sigexp) moduleOpt =
    let module_, inst = sigexp moduleOpt in
    StructDec (idOpt, module_, inst)

  let rec structdef (idOpt, strexp) None =
    let mid = strexpToStrexp strexp in
    StructDef (idOpt, mid)

  let rec structdecToStructDec (structdec, moduleOpt) = structdec moduleOpt

  type eqnTable = inst * Paths.region list ref IntTree.table

  let rec applyEqns wherecl namespace =
    let eqns = wherecl namespace in
    let table : eqnTable = IntTree.new_ 0 in
    let rec add (cid, Inst, r) =
      match IntTree.lookup table cid with
      | None -> IntTree.insert table (cid, ref [ (Inst, r) ])
      | Some rl -> rl := (Inst, r) :: !rl
    in
    let _ = List.app add eqns in
    let rec doInst = function
      | (Internal cid, r), condec -> (
          try
            ModSyn.strictify
              (ExtSyn.internalInst
                 (condec, ModSyn.abbrevify (cid, IntSyn.sgnLookup cid), r))
          with ExtSyn.Error msg ->
            raise
              (ExtSyn.Error
                 (msg ^ "\nin instantiation generated for_sml "
                 ^ Names.qidToString (Names.constQid cid))))
      | (External tm, r), condec ->
          ModSyn.strictify (ExtSyn.externalInst (condec, tm, r))
    in
    let rec transformConDec (cid, condec) =
      match IntTree.lookup table cid with
      | None -> condec
      | Some { contents = l } -> List.foldr doInst condec l
    in
    transformConDec

  let rec moduleWhere (module_, wherecl) =
    (* val _ = IntSyn.resetFrom (mark, markStruct) *)
    let mark, markStruct = IntSyn.sgnSize () in
    let module' = ModSyn.instantiateModule (module_, applyEqns wherecl) in
    let _ = Names.resetFrom (mark, markStruct) in
    module'
end
