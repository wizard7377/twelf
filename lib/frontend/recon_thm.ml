(* Reconstruct Termination Information *)
(* Author: Carsten Schuermann *)
(* Modified: Brigitte Pientka *)

functor (* GEN BEGIN FUNCTOR DECL *) ReconThm (structure Global : GLOBAL
                  (* structure IntSyn : INTSYN *)
                  structure Abstract : ABSTRACT
                  (*! sharing Abstract.IntSyn = IntSyn !*)
                  structure Constraints : CONSTRAINTS
                  structure Names : NAMES
                  (*! sharing Names.IntSyn = IntSyn !*)
                  (*! structure Paths' : PATHS !*)
                  structure ThmSyn': THMSYN
                    sharing ThmSyn'.Names = Names
                  structure ReconTerm': RECON_TERM
                  (*! sharing ReconTerm'.IntSyn = IntSyn !*)
                  (*! sharing ReconTerm'.Paths = Paths'  !*)
                  structure Print : PRINT
                  (*! sharing Print.IntSyn = IntSyn !*)
                    )
  : RECON_THM =
struct
  structure ThmSyn = ThmSyn'
  (*! structure Paths = Paths' !*)
  structure ExtSyn = ReconTerm'

  exception Error of string

  local
    structure M = ModeSyn
    structure I = IntSyn
    structure L = ThmSyn
    structure P = Paths
    structure T = ReconTerm'

    fun error (r, msg) = raise Error (P.wrap (r, msg))

    type order = ThmSyn.order * Paths.region

    fun varg (r, L) = (ThmSyn.Varg L, r)

    fun lex (r0, L) =
        let
          fun (* GEN BEGIN FUN FIRST *) lex' nil = (nil, r0) (* GEN END FUN FIRST *)
            | (* GEN BEGIN FUN BRANCH *) lex' ((O, r) :: L) =
              let
                (* GEN BEGIN TAG OUTSIDE LET *) val (Os, r') = lex' L (* GEN END TAG OUTSIDE LET *)
              in
                (O :: Os, Paths.join (r, r'))
              end (* GEN END FUN BRANCH *)
          (* GEN BEGIN TAG OUTSIDE LET *) val (Os, r1) = lex' L (* GEN END TAG OUTSIDE LET *)
        in
          (ThmSyn.Lex Os, r1)
        end

    fun simul (r0, L) =
        let
          fun (* GEN BEGIN FUN FIRST *) simul' nil = (nil, r0) (* GEN END FUN FIRST *)
            | (* GEN BEGIN FUN BRANCH *) simul' ((O, r) :: L) =
              let
                (* GEN BEGIN TAG OUTSIDE LET *) val (Os, r') = simul' L (* GEN END TAG OUTSIDE LET *)
              in
                (O :: Os, Paths.join (r, r'))
              end (* GEN END FUN BRANCH *)
          (* GEN BEGIN TAG OUTSIDE LET *) val (Os, r1) = simul' L (* GEN END TAG OUTSIDE LET *)
        in
          (ThmSyn.Simul Os, r1)
        end

    type callpats = (ThmSyn.callpats * Paths.region list)

    fun (* GEN BEGIN FUN FIRST *) checkArgNumber (0, I.Uni (I.Type), nil, r) = () (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) checkArgNumber (0, I.Pi (_, V2), arg::args, r) =
          checkArgNumber (0, V2, args, r) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) checkArgNumber (0, I.Pi (_, V2), nil, r) =
          error (r, "Missing arguments in call pattern") (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) checkArgNumber (0, I.Uni (I.Type), arg::args, r) =
          error (r, "Extraneous arguments in call pattern") (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) checkArgNumber (i, I.Pi (_, V2), args, r) =
          checkArgNumber (i-1, V2, args, r) (* GEN END FUN BRANCH *)
      (* everything else should be impossible! *)

    fun (* GEN BEGIN FUN FIRST *) checkCallPat (I.ConDec (_, _, i, I.Normal, V, I.Kind), P, r) =
          checkArgNumber (i, V, P, r) (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) checkCallPat (I.ConDec (a, _, _, I.Constraint _, _, _), P, r) =
          error (r, "Illegal constraint constant " ^ a ^ " in call pattern") (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) checkCallPat (I.ConDec (a, _, _, I.Foreign _, _, _), P, r) =
          error (r, "Illegal foreign constant " ^ a ^ " in call pattern") (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) checkCallPat (I.ConDec (a, _, _, _, _, I.Type), P, r) =
          error (r, "Constant " ^ a ^ " in call pattern not a type family") (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) checkCallPat (I.ConDef (a, _, _, _, _, _, _), P, r) =
          error (r, "Illegal defined constant " ^ a ^ " in call pattern") (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) checkCallPat (I.AbbrevDef (a, _, _, _, _, _), P, r) =
          error (r, "Illegal abbreviation " ^ a ^ " in call pattern") (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) checkCallPat (I.BlockDec (a, _, _, _), P, r) =
          error (r, "Illegal block identifier " ^ a ^ " in call pattern") (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) checkCallPat (I.SkoDec (a, _, _, _, _), P, r) =
          error (r, "Illegal Skolem constant " ^ a ^ " in call pattern") (* GEN END FUN BRANCH *)

    fun callpats L =
        let
          fun (* GEN BEGIN FUN FIRST *) callpats' nil = (nil, nil) (* GEN END FUN FIRST *)
            | (* GEN BEGIN FUN BRANCH *) callpats' ((name, P, r) :: L) =
              let
                (* GEN BEGIN TAG OUTSIDE LET *) val (cps, rs) = (callpats' L) (* GEN END TAG OUTSIDE LET *)
                (* GEN BEGIN TAG OUTSIDE LET *) val qid = Names.Qid (nil, name) (* GEN END TAG OUTSIDE LET *)
              in
                (* check whether they are families here? *)
                case Names.constLookup qid
                  of NONE => error (r, "Undeclared identifier "
                                    ^ Names.qidToString (valOf (Names.constUndef qid))
                                    ^ " in call pattern")
                   | SOME cid =>
                       (checkCallPat (I.sgnLookup cid, P, r);
                        ((cid, P) :: cps, (r :: rs)))
              end (* GEN END FUN BRANCH *)
          (* GEN BEGIN TAG OUTSIDE LET *) val (cps, rs) = callpats' L (* GEN END TAG OUTSIDE LET *)
        in
          (ThmSyn.Callpats (cps), rs)
        end

    type tdecl = ThmSyn.t_decl * (Paths.region * Paths.region list)
    fun tdecl ((O, r), (C, rs)) = (ThmSyn.TDecl (O, C), (r, rs))
    fun tdeclTotDecl T  = T

    (* -bp *)
    (* predicate *)
    type predicate = ThmSyn.predicate * Paths.region
    fun (* GEN BEGIN FUN FIRST *) predicate ("LESS", r) = (ThmSyn.Less, r) (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) predicate ("LEQ", r) =  (ThmSyn.Leq, r) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) predicate ("EQUAL", r) = (ThmSyn.Eq, r) (* GEN END FUN BRANCH *)

    (* reduces declaration *)
    type rdecl = ThmSyn.r_decl * (Paths.region * Paths.region list)
    fun rdecl ((P, r0), (O1,r1), (O2, r2), (C, rs)) =
        let
            (* GEN BEGIN TAG OUTSIDE LET *) val r = Paths.join (r1, r2) (* GEN END TAG OUTSIDE LET *)
        in
            (ThmSyn.RDecl (ThmSyn.RedOrder(P ,O1, O2), C), (Paths.join (r0, r), rs))
        end

    fun rdeclTorDecl T  = T

     (* tabled declaration *)
    type tableddecl = (ThmSyn.tabled_decl * Paths.region)
    fun tableddecl (name, r) =
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val qid = Names.Qid (nil, name) (* GEN END TAG OUTSIDE LET *)
        in
          (* check whether they are families here? *)
         case Names.constLookup qid
                  of NONE => error (r, "Undeclared identifier "
                                    ^ Names.qidToString (valOf (Names.constUndef qid))
                                    ^ " in call pattern")
                   | SOME cid =>    (ThmSyn.TabledDecl cid, r)
        end


    fun tableddeclTotabledDecl T  = T

    (* keepTable declaration *)
    type keep_tabledecl = (ThmSyn.keep_table_decl * Paths.region)
    fun keepTabledecl (name, r) =
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val qid = Names.Qid (nil, name) (* GEN END TAG OUTSIDE LET *)
        in
          (* check whether they are families here? *)
         case Names.constLookup qid
                  of NONE => error (r, "Undeclared identifier "
                                    ^ Names.qidToString (valOf (Names.constUndef qid))
                                    ^ " in call pattern")
                   | SOME cid =>    (ThmSyn.KeepTableDecl cid, r)
        end


    fun keepTabledeclToktDecl T  = T

    (* Theorem and prove declarations *)

    type prove = ThmSyn.p_decl * (Paths.region * Paths.region list)
    fun prove (n, (td, rrs)) = (ThmSyn.PDecl (n, td), rrs)
    fun proveToProve P = P

    type establish = ThmSyn.p_decl * (Paths.region * Paths.region list)
    fun establish (n, (td, rrs)) = (ThmSyn.PDecl (n, td), rrs)
    fun establishToEstablish P = P

    type assert = ThmSyn.callpats * Paths.region list
    fun assert (cp, rs) = (cp, rs)
    fun assertToAssert P = P

    type decs = ExtSyn.dec I.ctx
    (* GEN BEGIN TAG OUTSIDE LET *) val null = I.Null (* GEN END TAG OUTSIDE LET *)
    (* GEN BEGIN TAG OUTSIDE LET *) val decl = I.Decl (* GEN END TAG OUTSIDE LET *)

    type labeldec = decs * decs
    type thm = labeldec list * ExtSyn.dec I.ctx * ModeSyn.mode I.ctx * int

    type theorem = thm -> thm
    type theoremdec = string * theorem

    fun dec (name, t) = (name, t)

    fun (* GEN BEGIN FUN FIRST *) ctxAppend (G, I.Null) = G (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) ctxAppend (G, I.Decl (G', D)) = I.Decl (ctxAppend (G, G'), D) (* GEN END FUN BRANCH *)

    fun (* GEN BEGIN FUN FIRST *) ctxMap f (I.Null) = I.Null (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) ctxMap f (I.Decl (G, D)) = I.Decl (ctxMap f G, f D) (* GEN END FUN BRANCH *)

    fun ctxBlockToString (G0, (G1, G2)) =
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val _ = Names.varReset I.Null (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val G0' = Names.ctxName G0 (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val G1' = Names.ctxLUName G1 (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val G2' = Names.ctxLUName G2 (* GEN END TAG OUTSIDE LET *)
        in
          Print.ctxToString (I.Null, G0') ^ "\n"
          ^ (case G1' of I.Null => "" | _ => "some " ^ Print.ctxToString (G0', G1') ^ "\n")
          ^ "pi " ^ Print.ctxToString (ctxAppend (G0', G1'), G2')
        end

    fun (* GEN BEGIN FUN FIRST *) checkFreevars (I.Null, (G1, G2), r) = () (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) checkFreevars (G0, (G1, G2), r) =
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val _ = Names.varReset I.Null (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val G0' = Names.ctxName G0 (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val G1' = Names.ctxLUName G1 (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val G2' = Names.ctxLUName G2 (* GEN END TAG OUTSIDE LET *)
        in
          error (r, "Free variables in context block after term reconstruction:\n"
                 ^ ctxBlockToString (G0', (G1', G2')))
        end (* GEN END FUN BRANCH *)

    fun abstractCtxPair (g1, g2) =
        let
          (* each block reconstructed independent of others *)
          (* GEN BEGIN TAG OUTSIDE LET *) val r = (case (T.ctxRegion g1, T.ctxRegion g2)
                     of (SOME r1, SOME r2) => Paths.join (r1, r2)
                      | (_, SOME r2) => r2) (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val T.JWithCtx (G1, T.JWithCtx (G2, _)) =
                T.recon (T.jwithctx (g1, T.jwithctx (g2, T.jnothing))) (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val (G0, [G1', G2']) =        (* closed nf *)
              Abstract.abstractCtxs [G1, G2]
              handle Constraints.Error (C)
              => error (r, "Constraints remain in context block after term reconstruction:\n"
                        ^ ctxBlockToString (I.Null, (G1, G2)) ^ "\n"
                        ^ Print.cnstrsToString C) (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val _ = checkFreevars (G0, (G1', G2'), r) (* GEN END TAG OUTSIDE LET *)
        in
          (G1', G2')
        end

    fun top (GBs, g, M, k) = (GBs, g, M, k)

    fun exists (g', t) (GBs, g, M, k) =
          t (GBs, ctxAppend (g, g'),
             ctxAppend (M, ctxMap ((* GEN BEGIN FUNCTION EXPRESSION *) fn _ => M.Minus (* GEN END FUNCTION EXPRESSION *)) g'), k)

    fun forall (g', t) (GBs, g, M, k) =
          t (GBs, ctxAppend (g, g'),
             ctxAppend (M, ctxMap ((* GEN BEGIN FUNCTION EXPRESSION *) fn _ => M.Plus (* GEN END FUNCTION EXPRESSION *)) g'), k)

    fun forallStar (g', t) (GBs, g, M, _) =
          t (GBs, ctxAppend (g, g'),
             ctxAppend (M, ctxMap ((* GEN BEGIN FUNCTION EXPRESSION *) fn _ => M.Plus (* GEN END FUNCTION EXPRESSION *)) g'), I.ctxLength g')

    fun forallG (gbs, t:thm->thm) (_:thm):thm =
          t (gbs, I.Null, I.Null, 0)

    fun theoremToTheorem t =
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val (gbs, g, M, k) = t (nil, I.Null, I.Null, 0) (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val _ = Names.varReset IntSyn.Null (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val GBs = List.map abstractCtxPair gbs (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val T.JWithCtx (G, _) = T.recon (T.jwithctx (g, T.jnothing)) (* GEN END TAG OUTSIDE LET *)
        in
          L.ThDecl (GBs, G, M, k)
        end

    fun theoremDecToTheoremDec (name, t) =
          (name, theoremToTheorem t)

    (* World checker *)

    fun abstractWDecl W =
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val W' = List.map Names.Qid W (* GEN END TAG OUTSIDE LET *)
        in
          W'
        end

    type wdecl =  ThmSyn.w_decl * Paths.region list
    fun wdecl (W, (cp, rs)) = (ThmSyn.WDecl (abstractWDecl W, cp), rs)
    fun wdeclTowDecl T = T

  in
    (* avoid this re-copying? -fp *)
    type order = order
    (* GEN BEGIN TAG OUTSIDE LET *) val varg = varg (* GEN END TAG OUTSIDE LET *)
    (* GEN BEGIN TAG OUTSIDE LET *) val lex = lex (* GEN END TAG OUTSIDE LET *)
    (* GEN BEGIN TAG OUTSIDE LET *) val simul = simul (* GEN END TAG OUTSIDE LET *)

    type callpats = callpats
    (* GEN BEGIN TAG OUTSIDE LET *) val callpats = callpats (* GEN END TAG OUTSIDE LET *)

    type tdecl = tdecl
    (* GEN BEGIN TAG OUTSIDE LET *) val tdecl = tdecl (* GEN END TAG OUTSIDE LET *)

    (* -bp *)
    type predicate = predicate
    (* GEN BEGIN TAG OUTSIDE LET *) val predicate = predicate (* GEN END TAG OUTSIDE LET *)

    (* -bp *)
    type rdecl = rdecl
    (* GEN BEGIN TAG OUTSIDE LET *) val rdecl = rdecl (* GEN END TAG OUTSIDE LET *)

    type tableddecl = tableddecl
    (* GEN BEGIN TAG OUTSIDE LET *) val tableddecl = tableddecl (* GEN END TAG OUTSIDE LET *)

    type keep_tabledecl = keep_tabledecl
    (* GEN BEGIN TAG OUTSIDE LET *) val keepTabledecl = keepTabledecl (* GEN END TAG OUTSIDE LET *)

    type prove = prove
    (* GEN BEGIN TAG OUTSIDE LET *) val prove = prove (* GEN END TAG OUTSIDE LET *)

    type establish = establish
    (* GEN BEGIN TAG OUTSIDE LET *) val establish = establish (* GEN END TAG OUTSIDE LET *)

    type assert = assert
    (* GEN BEGIN TAG OUTSIDE LET *) val assert = assert (* GEN END TAG OUTSIDE LET *)

    (* GEN BEGIN TAG OUTSIDE LET *) val tdeclTotDecl = tdeclTotDecl (* GEN END TAG OUTSIDE LET *)
    (* GEN BEGIN TAG OUTSIDE LET *) val rdeclTorDecl = rdeclTorDecl (* GEN END TAG OUTSIDE LET *)

    (* GEN BEGIN TAG OUTSIDE LET *) val tableddeclTotabledDecl = tableddeclTotabledDecl (* GEN END TAG OUTSIDE LET *)
    (* GEN BEGIN TAG OUTSIDE LET *) val keepTabledeclToktDecl = keepTabledeclToktDecl (* GEN END TAG OUTSIDE LET *)

    (* GEN BEGIN TAG OUTSIDE LET *) val proveToProve = proveToProve (* GEN END TAG OUTSIDE LET *)
    (* GEN BEGIN TAG OUTSIDE LET *) val establishToEstablish = establishToEstablish (* GEN END TAG OUTSIDE LET *)
    (* GEN BEGIN TAG OUTSIDE LET *) val assertToAssert = assertToAssert (* GEN END TAG OUTSIDE LET *)

    type decs = decs
    (* GEN BEGIN TAG OUTSIDE LET *) val null = null (* GEN END TAG OUTSIDE LET *)
    (* GEN BEGIN TAG OUTSIDE LET *) val decl = decl (* GEN END TAG OUTSIDE LET *)

    type theorem = theorem
    (* GEN BEGIN TAG OUTSIDE LET *) val top = top (* GEN END TAG OUTSIDE LET *)
    (* GEN BEGIN TAG OUTSIDE LET *) val forallStar = forallStar (* GEN END TAG OUTSIDE LET *)
    (* GEN BEGIN TAG OUTSIDE LET *) val forall = forall (* GEN END TAG OUTSIDE LET *)
    (* GEN BEGIN TAG OUTSIDE LET *) val exists = exists (* GEN END TAG OUTSIDE LET *)
    (* GEN BEGIN TAG OUTSIDE LET *) val forallG = forallG (* GEN END TAG OUTSIDE LET *)
    (* GEN BEGIN TAG OUTSIDE LET *) val theoremToTheorem = theoremToTheorem (* GEN END TAG OUTSIDE LET *)

    type theoremdec = theoremdec
    (* GEN BEGIN TAG OUTSIDE LET *) val dec = dec (* GEN END TAG OUTSIDE LET *)
    (* GEN BEGIN TAG OUTSIDE LET *) val theoremDecToTheoremDec = theoremDecToTheoremDec (* GEN END TAG OUTSIDE LET *)

    type wdecl = wdecl
    (* GEN BEGIN TAG OUTSIDE LET *) val wdeclTowDecl = wdeclTowDecl (* GEN END TAG OUTSIDE LET *)
    (* GEN BEGIN TAG OUTSIDE LET *) val wdecl = wdecl (* GEN END TAG OUTSIDE LET *)
  end (* local *)
end (* GEN END FUNCTOR DECL *) (* functor ReconThm *)
