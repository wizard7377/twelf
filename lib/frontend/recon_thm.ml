open Basis
(* External Syntax for_sml meta theorems *)

(* Author: Carsten Schuermann *)

module type THMEXTSYN = sig
  module ExtSyn : Recon_term.EXTSYN

  (*! structure Paths : Paths.PATHS  !*)
  type order

  val varg : Paths.region * string list -> order
  val lex : Paths.region * order list -> order
  val simul : Paths.region * order list -> order

  type callpats

  val callpats : string * string option list * Paths.region list -> callpats

  type tdecl

  val tdecl : order * callpats -> tdecl

  (* -bp *)
  type predicate

  val predicate : string * Paths.region -> predicate

  (* -bp *)
  type rdecl

  val rdecl : predicate * order * order * callpats -> rdecl

  type tableddecl

  val tableddecl : string * Paths.region -> tableddecl

  type keepTabledecl

  val keepTabledecl : string * Paths.region -> keepTabledecl

  type prove

  val prove : int * tdecl -> prove

  type establish

  val establish : int * tdecl -> establish

  type assert_ml

  val assert_ml : callpats -> assert_ml

  type decs
  type theorem
  type theoremdec

  val null : decs
  val decl : decs * ExtSyn.dec -> decs
  val top : theorem
  val exists : decs * theorem -> theorem
  val forall : decs * theorem -> theorem
  val forallStar : decs * theorem -> theorem
  val forallG : decs * decs list * theorem -> theorem
  val dec : string * theorem -> theoremdec

  (* world checker *)
  type wdecl

  val wdecl : string list * string list * callpats -> wdecl
  (*  val wdecl : (decs * decs) list * callpats -> wdecl *)
end

(* signature Thm.THMEXTSYN *)

module type RECON_THM = sig
  module ThmSyn : Thm.Thmsyn.THMSYN
  include Thm.THMEXTSYN

  exception Error of string

  val tdeclTotDecl : tdecl -> ThmSyn.tDecl * (Paths.region * Paths.region list)
  val rdeclTorDecl : rdecl -> ThmSyn.rDecl * (Paths.region * Paths.region list)
  val tableddeclTotabledDecl : tableddecl -> ThmSyn.tabledDecl * Paths.region

  val keepTabledeclToktDecl :
    keepTabledecl -> ThmSyn.keepTableDecl * Paths.region

  val theoremToTheorem : theorem -> ThmSyn.thDecl
  val theoremDecToTheoremDec : theoremdec -> string * ThmSyn.thDecl
  val proveToProve : prove -> ThmSyn.pDecl * (Paths.region * Paths.region list)

  val establishToEstablish :
    establish -> ThmSyn.pDecl * (Paths.region * Paths.region list)

  val assertToAssert : assert_ml -> ThmSyn.callpats * Paths.region list
  val wdeclTowDecl : wdecl -> ThmSyn.wDecl * Paths.region list
end

(* signature RECON_THM *)
(* Reconstruct Termination Information *)

(* Author: Carsten Schuermann *)

(* Modified: Brigitte Pientka *)

module ReconThm
    (Global : Global.GLOBAL)
    (Abstract : Abstract.ABSTRACT)
    (Constraints : Constraints.CONSTRAINTS)
    (Names : Names.NAMES)
    (ThmSyn' : Thm.Thmsyn.THMSYN)
    (ReconTerm' : Recon_term.RECON_TERM)
    (Print : Print.PRINT) : RECON_THM = struct
  module ThmSyn = ThmSyn'
  (*! structure Paths = Paths' !*)

  module ExtSyn = ReconTerm'

  exception Error of string

  module M = ModeSyn
  module I = IntSyn
  module L = ThmSyn
  module P = Paths
  module T = ReconTerm'

  let rec error (r, msg) = raise (Error (P.wrap (r, msg)))

  type order = ThmSyn.order * Paths.region

  let rec varg (r, L) = (ThmSyn.Varg L, r)

  let rec lex (r0, L) =
    let rec lex' = function
      | [] -> ([], r0)
      | (O, r) :: L ->
          let Os, r' = lex' L in
          (O :: Os, Paths.join (r, r'))
    in
    let Os, r1 = lex' L in
    (ThmSyn.Lex Os, r1)

  let rec simul (r0, L) =
    let rec simul' = function
      | [] -> ([], r0)
      | (O, r) :: L ->
          let Os, r' = simul' L in
          (O :: Os, Paths.join (r, r'))
    in
    let Os, r1 = simul' L in
    (ThmSyn.Simul Os, r1)

  type callpats = ThmSyn.callpats * Paths.region list

  let rec checkArgNumber = function
    | 0, I.Uni I.Type, [], r -> ()
    | 0, I.Pi (_, V2), arg :: args, r -> checkArgNumber (0, V2, args, r)
    | 0, I.Pi (_, V2), [], r -> error (r, "Missing arguments in call pattern")
    | 0, I.Uni I.Type, arg :: args, r ->
        error (r, "Extraneous arguments in call pattern")
    | i, I.Pi (_, V2), args, r -> checkArgNumber (i - 1, V2, args, r)
  (* everything else should be impossible! *)

  let rec checkCallPat = function
    | I.ConDec (_, _, i, I.Normal, V, I.Kind), P, r ->
        checkArgNumber (i, V, P, r)
    | I.ConDec (a, _, _, I.Constraint _, _, _), P, r ->
        error (r, "Illegal constraint constant " ^ a ^ " in call pattern")
    | I.ConDec (a, _, _, I.Foreign _, _, _), P, r ->
        error (r, "Illegal foreign constant " ^ a ^ " in call pattern")
    | I.ConDec (a, _, _, _, _, I.Type), P, r ->
        error (r, "Constant " ^ a ^ " in call pattern not a type family")
    | I.ConDef (a, _, _, _, _, _, _), P, r ->
        error (r, "Illegal defined constant " ^ a ^ " in call pattern")
    | I.AbbrevDef (a, _, _, _, _, _), P, r ->
        error (r, "Illegal abbreviation " ^ a ^ " in call pattern")
    | I.BlockDec (a, _, _, _), P, r ->
        error (r, "Illegal block identifier " ^ a ^ " in call pattern")
    | I.SkoDec (a, _, _, _, _), P, r ->
        error (r, "Illegal Skolem constant " ^ a ^ " in call pattern")

  let rec callpats L =
    let rec callpats' = function
      | [] -> ([], [])
      | (name, P, r) :: L -> (
          let cps, rs = callpats' L in
          let qid = Names.Qid ([], name) in
          (* check whether they are families here? *)
          match Names.constLookup qid with
          | None ->
              error
                ( r,
                  "Undeclared identifier "
                  ^ Names.qidToString (valOf (Names.constUndef qid))
                  ^ " in call pattern" )
          | Some cid ->
              checkCallPat (I.sgnLookup cid, P, r);
              ((cid, P) :: cps, r :: rs))
    in
    let cps, rs = callpats' L in
    (ThmSyn.Callpats cps, rs)

  type tdecl = ThmSyn.tDecl * (Paths.region * Paths.region list)

  let rec tdecl ((O, r), (C, rs)) = (ThmSyn.TDecl (O, C), (r, rs))
  let rec tdeclTotDecl T = T
  (* -bp *)

  (* predicate *)

  type predicate = ThmSyn.predicate * Paths.region

  let rec predicate = function
    | "LESS", r -> (ThmSyn.Less, r)
    | "LEQ", r -> (ThmSyn.Leq, r)
    | "EQUAL", r -> (ThmSyn.Eq, r)
  (* reduces declaration *)

  type rdecl = ThmSyn.rDecl * (Paths.region * Paths.region list)

  let rec rdecl ((P, r0), (O1, r1), (O2, r2), (C, rs)) =
    let r = Paths.join (r1, r2) in
    (ThmSyn.RDecl (ThmSyn.RedOrder (P, O1, O2), C), (Paths.join (r0, r), rs))

  let rec rdeclTorDecl T = T
  (* tabled declaration *)

  type tableddecl = ThmSyn.tabledDecl * Paths.region

  let rec tableddecl (name, r) =
    let qid = Names.Qid ([], name) in
    (* check whether they are families here? *)
    match Names.constLookup qid with
    | None ->
        error
          ( r,
            "Undeclared identifier "
            ^ Names.qidToString (valOf (Names.constUndef qid))
            ^ " in call pattern" )
    | Some cid -> (ThmSyn.TabledDecl cid, r)

  let rec tableddeclTotabledDecl T = T
  (* keepTable declaration *)

  type keepTabledecl = ThmSyn.keepTableDecl * Paths.region

  let rec keepTabledecl (name, r) =
    let qid = Names.Qid ([], name) in
    (* check whether they are families here? *)
    match Names.constLookup qid with
    | None ->
        error
          ( r,
            "Undeclared identifier "
            ^ Names.qidToString (valOf (Names.constUndef qid))
            ^ " in call pattern" )
    | Some cid -> (ThmSyn.KeepTableDecl cid, r)

  let rec keepTabledeclToktDecl T = T
  (* Theorem and prove declarations *)

  type prove = ThmSyn.pDecl * (Paths.region * Paths.region list)

  let rec prove (n, (td, rrs)) = (ThmSyn.PDecl (n, td), rrs)
  let rec proveToProve P = P

  type establish = ThmSyn.pDecl * (Paths.region * Paths.region list)

  let rec establish (n, (td, rrs)) = (ThmSyn.PDecl (n, td), rrs)
  let rec establishToEstablish P = P

  type assert_ml = ThmSyn.callpats * Paths.region list

  let rec assert_ml (cp, rs) = (cp, rs)
  let rec assertToAssert P = P

  type decs = ExtSyn.dec I.ctx

  let null = I.Null
  let decl = I.Decl

  type labeldec = decs * decs
  type thm = labeldec list * ExtSyn.dec I.ctx * ModeSyn.mode I.ctx * int
  type theorem = thm -> thm
  type theoremdec = string * theorem

  let rec dec (name, t) = (name, t)

  let rec ctxAppend = function
    | G, I.Null -> G
    | G, I.Decl (G', D) -> I.Decl (ctxAppend (G, G'), D)

  let rec ctxMap = function
    | f, I.Null -> I.Null
    | f, I.Decl (G, D) -> I.Decl (ctxMap f G, f D)

  let rec ctxBlockToString (G0, (G1, G2)) =
    let _ = Names.varReset I.Null in
    let G0' = Names.ctxName G0 in
    let G1' = Names.ctxLUName G1 in
    let G2' = Names.ctxLUName G2 in
    Print.ctxToString (I.Null, G0')
    ^ "\n"
    ^ (match G1' with
      | I.Null -> ""
      | _ -> "some " ^ Print.ctxToString (G0', G1') ^ "\n")
    ^ "pi "
    ^ Print.ctxToString (ctxAppend (G0', G1'), G2')

  let rec checkFreevars = function
    | I.Null, (G1, G2), r -> ()
    | G0, (G1, G2), r ->
        let _ = Names.varReset I.Null in
        let G0' = Names.ctxName G0 in
        let G1' = Names.ctxLUName G1 in
        let G2' = Names.ctxLUName G2 in
        error
          ( r,
            "Free variables in context block after term reconstruction:\n"
            ^ ctxBlockToString (G0', (G1', G2')) )

  let rec abstractCtxPair (g1, g2) =
    (* each block reconstructed independent of others *)
    let r =
      match (T.ctxRegion g1, T.ctxRegion g2) with
      | Some r1, Some r2 -> Paths.join (r1, r2)
      | _, Some r2 -> r2
    in
    let (T.JWithCtx (G1, T.JWithCtx (G2, _))) =
      T.recon (T.jwithctx (g1, T.jwithctx (g2, T.jnothing)))
    in
    let G0, [ G1'; G2' ] =
      (* closed nf *)
      try Abstract.abstractCtxs [ G1; G2 ]
      with Constraints.Error C ->
        error
          ( r,
            "Constraints remain in context block after term reconstruction:\n"
            ^ ctxBlockToString (I.Null, (G1, G2))
            ^ "\n" ^ Print.cnstrsToString C )
    in
    let _ = checkFreevars (G0, (G1', G2'), r) in
    (G1', G2')

  let rec top (GBs, g, M, k) = (GBs, g, M, k)

  let rec exists (g', t) (GBs, g, M, k) =
    t (GBs, ctxAppend (g, g'), ctxAppend (M, ctxMap (fun _ -> M.Minus) g'), k)

  let rec forall (g', t) (GBs, g, M, k) =
    t (GBs, ctxAppend (g, g'), ctxAppend (M, ctxMap (fun _ -> M.Plus) g'), k)

  let rec forallStar (g', t) (GBs, g, M, _) =
    t
      ( GBs,
        ctxAppend (g, g'),
        ctxAppend (M, ctxMap (fun _ -> M.Plus) g'),
        I.ctxLength g' )

  let rec forallG ((gbs, t) : thm -> thm) (_ : thm) thm =
    t (gbs, I.Null, I.Null, 0)

  let rec theoremToTheorem t =
    let gbs, g, M, k = t ([], I.Null, I.Null, 0) in
    let _ = Names.varReset IntSyn.Null in
    let GBs = List.map abstractCtxPair gbs in
    let (T.JWithCtx (G, _)) = T.recon (T.jwithctx (g, T.jnothing)) in
    L.ThDecl (GBs, G, M, k)

  let rec theoremDecToTheoremDec (name, t) = (name, theoremToTheorem t)
  (* World checker *)

  let rec abstractWDecl W =
    let W' = List.map Names.Qid W in
    W'

  type wdecl = ThmSyn.wDecl * Paths.region list

  let rec wdecl (W, (cp, rs)) = (ThmSyn.WDecl (abstractWDecl W, cp), rs)
  let rec wdeclTowDecl T = T
  (* avoid this re-copying? -fp *)

  type order = order

  let varg = varg
  let lex = lex
  let simul = simul

  type callpats = callpats

  let callpats = callpats

  type tdecl = tdecl

  let tdecl = tdecl
  (* -bp *)

  type predicate = predicate

  let predicate = predicate
  (* -bp *)

  type rdecl = rdecl

  let rdecl = rdecl

  type tableddecl = tableddecl

  let tableddecl = tableddecl

  type keepTabledecl = keepTabledecl

  let keepTabledecl = keepTabledecl

  type prove = prove

  let prove = prove

  type establish = establish

  let establish = establish

  type assert_ml = assert_ml

  let assert_ml = assert_ml
  let tdeclTotDecl = tdeclTotDecl
  let rdeclTorDecl = rdeclTorDecl
  let tableddeclTotabledDecl = tableddeclTotabledDecl
  let keepTabledeclToktDecl = keepTabledeclToktDecl
  let proveToProve = proveToProve
  let establishToEstablish = establishToEstablish
  let assertToAssert = assertToAssert

  type decs = decs

  let null = null
  let decl = decl

  type theorem = theorem

  let top = top
  let forallStar = forallStar
  let forall = forall
  let exists = exists
  let forallG = forallG
  let theoremToTheorem = theoremToTheorem

  type theoremdec = theoremdec

  let dec = dec
  let theoremDecToTheoremDec = theoremDecToTheoremDec

  type wdecl = wdecl

  let wdeclTowDecl = wdeclTowDecl
  let wdecl = wdecl
  (* local *)
end

(* functor ReconThm *)
