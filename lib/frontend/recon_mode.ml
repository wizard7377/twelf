(* External Syntax of Mode Declarations *)

(* Author: Carsten Schuermann *)

module type EXTMODES = sig
  module ExtSyn : EXTSYN

  (*! structure Paths : PATHS  !*)
  type mode

  val plus : Paths.region -> mode
  val star : Paths.region -> mode
  val minus : Paths.region -> mode
  val minus1 : Paths.region -> mode

  type modedec

  module Short : sig
    type mterm
    type mspine

    val mnil : Paths.region -> mspine
    val mapp : (mode * string option) * mspine -> mspine
    val mroot : string list * string * Paths.region * mspine -> mterm
    val toModedec : mterm -> modedec
  end

  module Full : sig
    type mterm

    val mroot : ExtSyn.term * Paths.region -> mterm
    val mpi : mode * ExtSyn.dec * mterm -> mterm
    val toModedec : mterm -> modedec
  end
end

(* signature EXTMODES *)

module type RECON_MODE = sig
  (*! structure ModeSyn : MODESYN !*)
  include EXTMODES

  exception Error of string

  val modeToMode : modedec -> (IntSyn.cid * ModeSyn.modeSpine) * Paths.region
end

(* signature RECON_MODE *)
(* Reconstructing Mode Declarations *)

(* Author: Carsten Schuermann *)

module ReconMode
    (Global : GLOBAL)
    (Whnf : WHNF)
    (Names : NAMES)
    (ModePrint : MODEPRINT)
    (ModeDec : MODEDEC)
    (ReconTerm' : RECON_TERM) : RECON_MODE = struct
  (*! structure ModeSyn = ModeSyn' !*)

  module ExtSyn = ReconTerm'
  (*! structure Paths = Paths' !*)

  exception Error of string

  let rec error (r, msg) = raise (Error (Paths.wrap (r, msg)))

  module M = ModeSyn
  module I = IntSyn
  module T = ExtSyn
  module P = Paths

  type mode = M.mode * P.region

  let rec plus r = (M.Plus, r)
  let rec star r = (M.Star, r)
  let rec minus r = (M.Minus, r)
  let rec minus1 r = (M.Minus1, r)

  type modedec = (I.cid * M.modeSpine) * P.region

  module Short = struct
    type mterm = (I.cid * M.modeSpine) * P.region
    type mspine = M.modeSpine * P.region

    let rec mnil r = (M.Mnil, r)

    let rec mapp (((m, r1), name), (mS, r2)) =
      (M.Mapp (M.Marg (m, name), mS), P.join (r1, r2))

    let rec mroot (ids, id, r1, (mS, r2)) =
      let r = P.join (r1, r2) in
      let qid = Names.Qid (ids, id) in
      match Names.constLookup qid with
      | None ->
          error
            ( r,
              "Undeclared identifier "
              ^ Names.qidToString (valOf (Names.constUndef qid))
              ^ " in mode declaration" )
      | Some cid -> ((cid, ModeDec.shortToFull (cid, mS, r)), r)

    let rec toModedec nmS = nmS
  end
  (* structure Short *)

  module Full = struct
    type mterm = T.dec I.ctx * M.mode I.ctx -> (I.cid * M.modeSpine) * P.region

    let rec mpi ((m, _), d, t) (g, D) = t (I.Decl (g, d), I.Decl (D, m))

    let rec mroot (tm, r) (g, D) =
      (* convert term spine to mode spine *)
      (* Each argument must be contractible to variable *)
      (* convert root expression to head constant and mode spine *)
      (* convertExp (I.Root (I.Skonst _, S)) can't occur *)
      let (T.JWithCtx (G, T.JOf ((V, _), _, _))) =
        T.recon (T.jwithctx (g, T.jof (tm, T.typ r)))
      in
      let _ = T.checkErrors r in
      let rec convertSpine = function
        | I.Nil -> M.Mnil
        | I.App (U, S) ->
            (* print U? -fp *)
            (* yes, print U. -gaw *)
            let k =
              try Whnf.etaContract U
              with Whnf.Eta ->
                error
                  (r, "Argument " ^ Print.expToString (G, U) ^ " not a variable")
            in
            let (I.Dec (name, _)) = I.ctxLookup (G, k) in
            let mode = I.ctxLookup (D, k) in
            M.Mapp (M.Marg (mode, name), convertSpine S)
      in
      let rec convertExp = function
        | I.Root (I.Const a, S) -> (a, convertSpine S)
        | I.Root (I.Def d, S) -> (d, convertSpine S)
        | _ -> error (r, "Call pattern not an atomic type")
      in
      let a, mS = convertExp (Whnf.normalize (V, I.id)) in
      ModeDec.checkFull (a, mS, r);
      ((a, mS), r)

    let rec toModedec t =
      let _ = Names.varReset I.Null in
      let t' = t (I.Null, I.Null) in
      t'
  end
  (* structure Full *)

  let rec modeToMode (m, r) = (m, r)

  type mode = mode

  let plus = plus
  let star = star
  let minus = minus
  let minus1 = minus1

  type modedec = modedec

  module Short = Short
  module Full = Full

  let modeToMode = modeToMode
  (* local ... *)
end

(* functor ReconMode *)
