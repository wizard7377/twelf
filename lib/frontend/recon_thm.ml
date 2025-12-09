(* Reconstruct Termination Information *)
(* Author: Carsten Schuermann *)
(* Modified: Brigitte Pientka *)

module ReconThm (Global : GLOBAL)
                  (* (IntSyn : INTSYN) *)
                  (Abstract : ABSTRACT)
                  (*! sharing Abstract.IntSyn = IntSyn !*)
                  (Constraints : CONSTRAINTS)
                  (Names : NAMES)
                  (*! sharing Names.IntSyn = IntSyn !*)
                  (*! module Paths' : PATHS !*)
                  module ThmSyn': THMSYN
                    sharing ThmSyn'.Names = Names
                  module ReconTerm': RECON_TERM
                  (*! sharing ReconTerm'.IntSyn = IntSyn !*)
                  (*! sharing ReconTerm'.Paths = Paths'  !*)
                  (Print : PRINT): RECON_THM =
                  (*! sharing Print.IntSyn = IntSyn !*)
struct
  module ThmSyn = ThmSyn'
  (*! module Paths = Paths' !*)
  module ExtSyn = ReconTerm'

  exception Error of string

  local
    module M = ModeSyn
    module I = IntSyn
    module L = ThmSyn
    module P = Paths
    module T = ReconTerm'

    let rec error (r, msg) = raise Error (P.wrap (r, msg))

    type order = ThmSyn.Order * Paths.region

    let rec varg (r, L) = (ThmSyn.Varg L, r)

    let rec lex (r0, L) =
        let
          let rec lex' = function nil -> (nil, r0)
            | ((O, r) :: L) -> 
              let
                let (Os, r') = lex' L
              in
                (O :: Os, Paths.join (r, r'))
              end
          let (Os, r1) = lex' L
        in
          (ThmSyn.Lex Os, r1)
        end

    let rec simul (r0, L) =
        let
          let rec simul' = function nil -> (nil, r0)
            | ((O, r) :: L) -> 
              let
                let (Os, r') = simul' L
              in
                (O :: Os, Paths.join (r, r'))
              end
          let (Os, r1) = simul' L
        in
          (ThmSyn.Simul Os, r1)
        end

    type callpats = (ThmSyn.callpats * Paths.region list)

    let rec checkArgNumber = function (0, I.Uni (I.Type), nil, r) -> ()
      | (0, I.Pi (_, V2), arg::args, r) -> 
          checkArgNumber (0, V2, args, r)
      | (0, I.Pi (_, V2), nil, r) -> 
          error (r, "Missing arguments in call pattern")
      | (0, I.Uni (I.Type), arg::args, r) -> 
          error (r, "Extraneous arguments in call pattern")
      | (i, I.Pi (_, V2), args, r) -> 
          checkArgNumber (i-1, V2, args, r)
      (* everything else should be impossible! *)

    let rec checkCallPat = function (I.ConDec (_, _, i, I.Normal, V, I.Kind), P, r) -> 
          checkArgNumber (i, V, P, r)
      | (I.ConDec (a, _, _, I.Constraint _, _, _), P, r) -> 
          error (r, "Illegal constraint constant " ^ a ^ " in call pattern")
      | (I.ConDec (a, _, _, I.Foreign _, _, _), P, r) -> 
          error (r, "Illegal foreign constant " ^ a ^ " in call pattern")
      | (I.ConDec (a, _, _, _, _, I.Type), P, r) -> 
          error (r, "Constant " ^ a ^ " in call pattern not a type family")
      | (I.ConDef (a, _, _, _, _, _, _), P, r) -> 
          error (r, "Illegal defined constant " ^ a ^ " in call pattern")
      | (I.AbbrevDef (a, _, _, _, _, _), P, r) -> 
          error (r, "Illegal abbreviation " ^ a ^ " in call pattern")
      | (I.BlockDec (a, _, _, _), P, r) -> 
          error (r, "Illegal block identifier " ^ a ^ " in call pattern")
      | (I.SkoDec (a, _, _, _, _), P, r) -> 
          error (r, "Illegal Skolem constant " ^ a ^ " in call pattern")

    let rec callpats L =
        let
          let rec callpats' = function nil -> (nil, nil)
            | ((name, P, r) :: L) -> 
              let
                let (cps, rs) = (callpats' L)
                let qid = Names.Qid (nil, name)
              in
                (* check whether they are families here? *)
                case Names.constLookup qid
                  of NONE => error (r, "Undeclared identifier "
                                    ^ Names.qidToString (valOf (Names.constUndef qid))
                                    ^ " in call pattern")
                   | SOME cid =>
                       (checkCallPat (I.sgnLookup cid, P, r);
                        ((cid, P) :: cps, (r :: rs)))
              end
          let (cps, rs) = callpats' L
        in
          (ThmSyn.Callpats (cps), rs)
        end

    type tdecl = ThmSyn.tDecl * (Paths.region * Paths.region list)
    let rec tdecl ((O, r), (C, rs)) = (ThmSyn.TDecl (O, C), (r, rs))
    let rec tdeclTotDecl T  = T

    (* -bp *)
    (* predicate *)
    type predicate = ThmSyn.predicate * Paths.region
    let rec predicate = function ("LESS", r) -> (ThmSyn.Less, r)
      | ("LEQ", r) -> (ThmSyn.Leq, r)
      | ("EQUAL", r) -> (ThmSyn.Eq, r)

    (* reduces declaration *)
    type rdecl = ThmSyn.rDecl * (Paths.region * Paths.region list)
    let rec rdecl ((P, r0), (O1,r1), (O2, r2), (C, rs)) =
        let
            let r = Paths.join (r1, r2)
        in
            (ThmSyn.RDecl (ThmSyn.RedOrder(P ,O1, O2), C), (Paths.join (r0, r), rs))
        end

    let rec rdeclTorDecl T  = T

     (* tabled declaration *)
    type tableddecl = (ThmSyn.tabledDecl * Paths.region)
    let rec tableddecl (name, r) =
        let
          let qid = Names.Qid (nil, name)
        in
          (* check whether they are families here? *)
         case Names.constLookup qid
                  of NONE => error (r, "Undeclared identifier "
                                    ^ Names.qidToString (valOf (Names.constUndef qid))
                                    ^ " in call pattern")
                   | SOME cid =>    (ThmSyn.TabledDecl cid, r)
        end


    let rec tableddeclTotabledDecl T  = T

    (* keepTable declaration *)
    type keepTabledecl = (ThmSyn.keepTableDecl * Paths.region)
    let rec keepTabledecl (name, r) =
        let
          let qid = Names.Qid (nil, name)
        in
          (* check whether they are families here? *)
         case Names.constLookup qid
                  of NONE => error (r, "Undeclared identifier "
                                    ^ Names.qidToString (valOf (Names.constUndef qid))
                                    ^ " in call pattern")
                   | SOME cid =>    (ThmSyn.KeepTableDecl cid, r)
        end


    let rec keepTabledeclToktDecl T  = T

    (* Theorem and prove declarations *)

    type prove = ThmSyn.pDecl * (Paths.region * Paths.region list)
    let rec prove (n, (td, rrs)) = (ThmSyn.PDecl (n, td), rrs)
    let rec proveToProve P = P

    type establish = ThmSyn.pDecl * (Paths.region * Paths.region list)
    let rec establish (n, (td, rrs)) = (ThmSyn.PDecl (n, td), rrs)
    let rec establishToEstablish P = P

    type assert = ThmSyn.callpats * Paths.region list
    let rec assert (cp, rs) = (cp, rs)
    let rec assertToAssert P = P

    type decs = ExtSyn.dec I.Ctx
    let null = I.Null
    let decl = I.Decl

    type labeldec = decs * decs
    type thm = labeldec list * ExtSyn.dec I.Ctx * ModeSyn.Mode I.Ctx * int

    type theorem = thm -> thm
    type theoremdec = string * theorem

    let rec dec (name, t) = (name, t)

    let rec ctxAppend = function (G, I.Null) -> G
      | (G, I.Decl (G', D)) -> I.Decl (ctxAppend (G, G'), D)

    let rec ctxMap = function f (I.Null) -> I.Null
      | f (I.Decl (G, D)) -> I.Decl (ctxMap f G, f D)

    let rec ctxBlockToString (G0, (G1, G2)) =
        let
          let _ = Names.varReset I.Null
          let G0' = Names.ctxName G0
          let G1' = Names.ctxLUName G1
          let G2' = Names.ctxLUName G2
        in
          Print.ctxToString (I.Null, G0') ^ "\n"
          ^ (case G1' of I.Null => "" | _ => "some " ^ Print.ctxToString (G0', G1') ^ "\n")
          ^ "pi " ^ Print.ctxToString (ctxAppend (G0', G1'), G2')
        end

    let rec checkFreevars = function (I.Null, (G1, G2), r) -> ()
      | (G0, (G1, G2), r) -> 
        let
          let _ = Names.varReset I.Null
          let G0' = Names.ctxName G0
          let G1' = Names.ctxLUName G1
          let G2' = Names.ctxLUName G2
        in
          error (r, "Free variables in context block after term reconstruction:\n"
                 ^ ctxBlockToString (G0', (G1', G2')))
        end

    let rec abstractCtxPair (g1, g2) =
        let
          (* each block reconstructed independent of others *)
          let r = (case (T.ctxRegion g1, T.ctxRegion g2)
                     of (SOME r1, SOME r2) => Paths.join (r1, r2)
                      | (_, SOME r2) => r2)
          let T.JWithCtx (G1, T.JWithCtx (G2, _)) =
                T.recon (T.jwithctx (g1, T.jwithctx (g2, T.jnothing)))
          let (G0, [G1', G2']) =        (* closed nf *)
              Abstract.abstractCtxs [G1, G2]
              handle Constraints.Error (C)
              => error (r, "Constraints remain in context block after term reconstruction:\n"
                        ^ ctxBlockToString (I.Null, (G1, G2)) ^ "\n"
                        ^ Print.cnstrsToString C)
          let _ = checkFreevars (G0, (G1', G2'), r)
        in
          (G1', G2')
        end

    let rec top (GBs, g, M, k) = (GBs, g, M, k)

    let rec exists (g', t) (GBs, g, M, k) =
          t (GBs, ctxAppend (g, g'),
             ctxAppend (M, ctxMap (fun _ -> M.Minus) g'), k)

    let rec forall (g', t) (GBs, g, M, k) =
          t (GBs, ctxAppend (g, g'),
             ctxAppend (M, ctxMap (fun _ -> M.Plus) g'), k)

    let rec forallStar (g', t) (GBs, g, M, _) =
          t (GBs, ctxAppend (g, g'),
             ctxAppend (M, ctxMap (fun _ -> M.Plus) g'), I.ctxLength g')

    fun forallG (gbs, t:thm->thm) (_:thm):thm =
          t (gbs, I.Null, I.Null, 0)

    let rec theoremToTheorem t =
        let
          let (gbs, g, M, k) = t (nil, I.Null, I.Null, 0)
          let _ = Names.varReset IntSyn.Null
          let GBs = List.map abstractCtxPair gbs
          let T.JWithCtx (G, _) = T.recon (T.jwithctx (g, T.jnothing))
        in
          L.ThDecl (GBs, G, M, k)
        end

    let rec theoremDecToTheoremDec (name, t) =
          (name, theoremToTheorem t)

    (* World checker *)

    let rec abstractWDecl W =
        let
          let W' = List.map Names.Qid W
        in
          W'
        end

    type wdecl =  ThmSyn.wDecl * Paths.region list
    let rec wdecl (W, (cp, rs)) = (ThmSyn.WDecl (abstractWDecl W, cp), rs)
    let rec wdeclTowDecl T = T

  in
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

    type assert = assert
    let assert = assert

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
  end (* local *)
end (* functor ReconThm *)
