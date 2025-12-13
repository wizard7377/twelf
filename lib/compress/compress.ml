functor (* GEN BEGIN FUNCTOR DECL *) Compress (structure Global : GLOBAL) =
struct

  structure I = IntSyn
  structure S = Syntax
  structure Sgn = Sgn

  exception Unimp
  exception NoModes (* modes are not appropriate for the given I.ConDec *)

  (* GEN BEGIN TAG OUTSIDE LET *) val debug = ref ~1 (* GEN END TAG OUTSIDE LET *)

  fun sgnReset () = Sgn.clear ()

(* xlate_type : IntSyn.Exp -> Syntax.tp *)
  fun (* GEN BEGIN FUN FIRST *) xlate_type (I.Pi ((I.Dec(_, e1), _), e2)) = S.TPi(S.MINUS, xlate_type e1, xlate_type e2) (* GEN END FUN FIRST *)
    | (* GEN BEGIN FUN BRANCH *) xlate_type (I.Root (I.Const cid, sp)) = S.TRoot(cid, xlate_spine sp) (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) xlate_type (I.Root (I.Def cid, sp)) = S.TRoot(cid, xlate_spine sp) (* GEN END FUN BRANCH *) (* assuming cids of consts and defs to be disjoint *)
    | (* GEN BEGIN FUN BRANCH *) xlate_type (I.Root (I.NSDef cid, sp)) = S.TRoot(cid, xlate_spine sp) (* GEN END FUN BRANCH *)  (* ditto *)
    | (* GEN BEGIN FUN BRANCH *) xlate_type (I.Lam (_, t)) = xlate_type t (* GEN END FUN BRANCH *)  (* for type definitions, simply strip off the lambdas and leave
                                                   the variables free*)
  and (* GEN BEGIN FUN FIRST *) xlate_spine I.Nil = [] (* GEN END FUN FIRST *)
    | (* GEN BEGIN FUN BRANCH *) xlate_spine (I.App(e, s)) = xlate_spinelt e :: xlate_spine s (* GEN END FUN BRANCH *)
  and xlate_spinelt e  = S.Elt(xlate_term e)
  and (* GEN BEGIN FUN FIRST *) xlate_term (I.Root (I.Const cid, sp)) = S.ATerm(S.ARoot(S.Const cid, xlate_spine sp)) (* GEN END FUN FIRST *)
    | (* GEN BEGIN FUN BRANCH *) xlate_term (I.Root (I.Def cid, sp)) = S.ATerm(S.ARoot(S.Const cid, xlate_spine sp)) (* GEN END FUN BRANCH *) (* assuming cids of consts and defs to be disjoint *)
    | (* GEN BEGIN FUN BRANCH *) xlate_term (I.Root (I.NSDef cid, sp)) = S.ATerm(S.ARoot(S.Const cid, xlate_spine sp)) (* GEN END FUN BRANCH *) (* ditto *)
    | (* GEN BEGIN FUN BRANCH *) xlate_term (I.Root (I.BVar vid, sp)) = S.ATerm(S.ARoot(S.Var (vid - 1), xlate_spine sp)) (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) xlate_term (I.Lam (_, e)) = S.NTerm(S.Lam (xlate_term e)) (* GEN END FUN BRANCH *)
(* xlate_kind : IntSyn.Exp -> Syntax.knd *)
  fun (* GEN BEGIN FUN FIRST *) xlate_kind (I.Pi ((I.Dec(_, e1), _), e2)) = S.KPi(S.MINUS, xlate_type e1, xlate_kind e2) (* GEN END FUN FIRST *)
    | (* GEN BEGIN FUN BRANCH *) xlate_kind (I.Uni(I.Type)) = S.Type (* GEN END FUN BRANCH *)

  local open Syntax in
  (* simple skeletal form of types
     omits all dependencies, type constants *)
  datatype simple_tp = Base | Arrow of simple_tp * simple_tp

  fun (* GEN BEGIN FUN FIRST *) simplify_tp (TPi (_, t1, t2)) = Arrow(simplify_tp t1, simplify_tp t2) (* GEN END FUN FIRST *)
    | (* GEN BEGIN FUN BRANCH *) simplify_tp (TRoot _) = Base (* GEN END FUN BRANCH *)
  fun (* GEN BEGIN FUN FIRST *) simplify_knd (KPi (_, t1, k2)) = Arrow(simplify_tp t1, simplify_knd k2) (* GEN END FUN FIRST *)
    | (* GEN BEGIN FUN BRANCH *) simplify_knd (Type) = Base (* GEN END FUN BRANCH *)

  (* hereditarily perform some eta-expansions on
     a (term, type, spine, etc.) in a context
    (and if not synthesizing) at a simple type.

    The only type of eta-expansion performed is when we
    encounter
    x . (M_1, M_2, ... M_n)
    for a variable x, and M_1, ..., M_n have fewer lambda abstractions
    than their (skeletal) type would suggest.

    The complication with doing full eta-expansion is that if
    we were to wrap lambda abstractions around terms that occur
    in a synthesizing position, we would need to add ascriptions,
    and thus carry full types around everywhere.

    Fortunately, this weakened form of eta-expansion is all
    we need to reconcile the discrepancy between what twelf
    maintains as an invariant, and full eta-longness. *)
  fun (* GEN BEGIN FUN FIRST *) eta_expand_term G (NTerm t) T = NTerm(eta_expand_nterm G t T) (* GEN END FUN FIRST *)
    | (* GEN BEGIN FUN BRANCH *) eta_expand_term G (ATerm t) T = ATerm(eta_expand_aterm G t) (* GEN END FUN BRANCH *)
  and (* GEN BEGIN FUN FIRST *) eta_expand_nterm G (Lam t) (Arrow(t1, t2)) = Lam(eta_expand_term (t1::G) t t2) (* GEN END FUN FIRST *)
    | (* GEN BEGIN FUN BRANCH *) eta_expand_nterm G (NRoot (h,s)) T = NRoot(h, eta_expand_spine G s T) (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) eta_expand_nterm G (Lam t) Base = raise Syntax "Lambda occurred where term of base type expected" (* GEN END FUN BRANCH *)
  and (* GEN BEGIN FUN FIRST *) eta_expand_aterm G (ARoot (Const n, s)) =
      let
          (* GEN BEGIN TAG OUTSIDE LET *) val stp = simplify_tp(typeOf (Sgn.o_classifier n)) (* GEN END TAG OUTSIDE LET *)
      in
          ARoot(Const n, eta_expand_spine G s stp)
      end (* GEN END FUN FIRST *)
    | (* GEN BEGIN FUN BRANCH *) eta_expand_aterm G (ARoot (Var n, s)) =
      let
          (* GEN BEGIN TAG OUTSIDE LET *) val stp = List.nth(G, n) (* GEN END TAG OUTSIDE LET *)
      in
          ARoot(Var n, eta_expand_var_spine G s stp)
      end (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) eta_expand_aterm G (ERoot _) = raise Syntax "invariant violated in eta_expand_aterm" (* GEN END FUN BRANCH *)
  and (* GEN BEGIN FUN FIRST *) eta_expand_tp G (TRoot(n, s)) =
      let
          (* GEN BEGIN TAG OUTSIDE LET *) val stp = simplify_knd(kindOf (Sgn.o_classifier n)) (* GEN END TAG OUTSIDE LET *)
      in
          TRoot(n, eta_expand_spine G s stp)
      end (* GEN END FUN FIRST *)
    | (* GEN BEGIN FUN BRANCH *) eta_expand_tp G (TPi(m,a,b)) = TPi(m,eta_expand_tp G a, eta_expand_tp (simplify_tp a::G) b) (* GEN END FUN BRANCH *)
  and (* GEN BEGIN FUN FIRST *) eta_expand_knd G (Type) = Type (* GEN END FUN FIRST *)
    | (* GEN BEGIN FUN BRANCH *) eta_expand_knd G (KPi(m,a,b)) = KPi(m,eta_expand_tp G a, eta_expand_knd (simplify_tp a::G) b) (* GEN END FUN BRANCH *)
  and (* GEN BEGIN FUN FIRST *) eta_expand_spine G [] Base = [] (* GEN END FUN FIRST *) (* this seems risky, but okay as long as the only eta-shortness we find is in variable-headed pattern spines *)
    | (* GEN BEGIN FUN BRANCH *) eta_expand_spine G ((Elt m)::tl) (Arrow(t1, t2)) =
      Elt(eta_expand_term G m t1) :: eta_expand_spine G tl t2 (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) eta_expand_spine G ((AElt m)::tl) (Arrow(t1, t2)) =
      AElt(eta_expand_aterm G m) :: eta_expand_spine G tl t2 (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) eta_expand_spine G ((Ascribe(m,a))::tl) (Arrow(t1, t2)) =
      Ascribe(eta_expand_nterm G m t1, eta_expand_tp G a) :: eta_expand_spine G tl t2 (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) eta_expand_spine G (Omit::tl) (Arrow(t1,t2)) =
      Omit :: eta_expand_spine G tl t2 (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) eta_expand_spine _ _ _ = raise Syntax "Can't figure out how to eta expand spine" (* GEN END FUN BRANCH *)
  (* the behavior here is that we are eta-expanding all of the elements of the spine, not the head of *this* spine *)
  and (* GEN BEGIN FUN FIRST *) eta_expand_var_spine G [] _ = [] (* GEN END FUN FIRST *) (* in fact this spine may not be eta-long yet *)
    | (* GEN BEGIN FUN BRANCH *) eta_expand_var_spine G ((Elt m)::tl) (Arrow(t1, t2)) =
      Elt(eta_expand_immediate (eta_expand_term G m t1, t1)) :: eta_expand_spine G tl t2 (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) eta_expand_var_spine _ _ _ = raise Syntax "Can't figure out how to eta expand var-headed spine" (* GEN END FUN BRANCH *)
  (* here's where the actual expansion takes place *)
  and (* GEN BEGIN FUN FIRST *) eta_expand_immediate (m, Base) = m (* GEN END FUN FIRST *)
    | (* GEN BEGIN FUN BRANCH *) eta_expand_immediate (NTerm(Lam m), Arrow(t1, t2)) =
      NTerm(Lam(eta_expand_immediate(m, t2))) (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) eta_expand_immediate (m, Arrow(t1, t2)) =
      let
          (* GEN BEGIN TAG OUTSIDE LET *) val variable = eta_expand_immediate(ATerm(ARoot(Var 0, [])), t1) (* GEN END TAG OUTSIDE LET *)
      in
          NTerm(Lam(eta_expand_immediate(apply_to(shift m, variable), t2)))
      end (* GEN END FUN BRANCH *)
  and (* GEN BEGIN FUN FIRST *) apply_to (ATerm(ARoot(h, s)), m) = ATerm(ARoot(h, s @ [Elt m])) (* GEN END FUN FIRST *)
    | (* GEN BEGIN FUN BRANCH *) apply_to (NTerm(NRoot(h, s)), m) = NTerm(NRoot(h, s @ [Elt m])) (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) apply_to _ = raise Syntax "Invariant violated in apply_to" (* GEN END FUN BRANCH *)
  end

  (* GEN BEGIN TAG OUTSIDE LET *) val typeOf = S.typeOf (* GEN END TAG OUTSIDE LET *)
  (* GEN BEGIN TAG OUTSIDE LET *) val kindOf = S.kindOf (* GEN END TAG OUTSIDE LET *)

  exception Debug of S.spine * S.tp * S.tp
 (* val compress_type : Syntax.tp list -> Syntax.mode list option * Syntax.tp -> Syntax.tp *)
 (* the length of the mode list, if there is one, should correspond to the number of pis in the input type.
    however, as indicated in the XXX comment below, it seems necessary to treat SOME of empty list
    as if it were NONE. This doesn't seem right. *)
  fun compress_type G s = (* if !debug < 0
                          then *) compress_type' G s
                          (* else  (if !debug = 0 then raise Debug(G, s) else ();
                                debug := !debug - 1; compress_type' G s) *)
  and (* GEN BEGIN FUN FIRST *) compress_type' G (NONE, S.TPi(_, a, b)) = S.TPi(S.MINUS, compress_type G (NONE, a), compress_type (a::G) (NONE, b)) (* GEN END FUN FIRST *)
    | (* GEN BEGIN FUN BRANCH *) compress_type' G (SOME (m::ms), S.TPi(_, a, b)) = S.TPi(m, compress_type G (NONE, a), compress_type (a::G) (SOME ms, b)) (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) compress_type' G (SOME [], S.TRoot(cid, sp)) = S.TRoot(cid, compress_type_spine G (sp,
                                                                                   kindOf(Sgn.o_classifier cid),
                                                                                   kindOf(Sgn.classifier cid))) (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) compress_type' G (NONE, a as S.TRoot _) = compress_type G (SOME [], a) (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) compress_type' G (SOME [], a as S.TPi _) = compress_type G (NONE, a) (* GEN END FUN BRANCH *) (* XXX sketchy *)

(* XXX: optimization: don't compute mstar if omit? *)
  and (* GEN BEGIN FUN FIRST *) compress_type_spine G ([], w, wstar) = [] (* GEN END FUN FIRST *)
    | (* GEN BEGIN FUN BRANCH *) compress_type_spine G ((S.Elt m)::sp, S.KPi(_, a, v), S.KPi(mode, astar, vstar)) =
      let
          (* GEN BEGIN TAG OUTSIDE LET *) val mstar = compress_term G (m, a) (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val sstar = compress_type_spine G (sp,
                                        S.subst_knd (S.TermDot(m, a, S.Id)) v,
                                        S.subst_knd (S.TermDot(mstar, astar, S.Id)) vstar) (* GEN END TAG OUTSIDE LET *)
      in
          case (mode, mstar) of
              (S.OMIT, _) => S.Omit::sstar
            | (S.MINUS, _) => S.Elt mstar::sstar
            | (S.PLUS, S.ATerm t) => S.AElt t::sstar
            | (S.PLUS, S.NTerm t) => S.Ascribe(t, compress_type G (NONE, a))::sstar
      end (* GEN END FUN BRANCH *)
  and (* GEN BEGIN FUN FIRST *) compress_spine G ([], w, wstar) = [] (* GEN END FUN FIRST *)
    | (* GEN BEGIN FUN BRANCH *) compress_spine G ((S.Elt m)::sp, S.TPi(_, a, v), S.TPi(mode, astar, vstar)) =
      let
          (* GEN BEGIN TAG OUTSIDE LET *) val mstar = compress_term G (m, a) (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val sstar = compress_spine G (sp,
                                        S.subst_tp (S.TermDot(m, a, S.Id)) v,
                                        S.subst_tp (S.TermDot(mstar, astar, S.Id)) vstar) (* GEN END TAG OUTSIDE LET *)
      in
          case (mode, mstar) of
              (S.OMIT, _) => S.Omit::sstar
            | (S.MINUS, _) => S.Elt mstar::sstar
            | (S.PLUS, S.ATerm t) => S.AElt t::sstar
            | (S.PLUS, S.NTerm t) => S.Ascribe(t, compress_type G (NONE, a))::sstar
      end (* GEN END FUN BRANCH *)
  and (* GEN BEGIN FUN FIRST *) compress_term G (S.ATerm(S.ARoot(S.Var n, sp)), _) =
      let
          (* GEN BEGIN TAG OUTSIDE LET *) val a = S.ctxLookup(G, n) (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val astar = compress_type G (NONE, a) (* GEN END TAG OUTSIDE LET *)
      in
          S.ATerm(S.ARoot(S.Var n, compress_spine G (sp, a, astar)))
      end (* GEN END FUN FIRST *)
    | (* GEN BEGIN FUN BRANCH *) compress_term G (S.ATerm(S.ARoot(S.Const n, sp)), _) =
      let
          (* GEN BEGIN TAG OUTSIDE LET *) val a = typeOf (Sgn.o_classifier n) (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val astar = typeOf (Sgn.classifier n) (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val term_former = case Sgn.get_p n of
                                SOME false => S.NTerm o S.NRoot
                              | _ => S.ATerm o S.ARoot (* GEN END TAG OUTSIDE LET *)
      in
          term_former(S.Const n, compress_spine G (sp, a, astar))
      end (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) compress_term G (S.NTerm(S.Lam t),S.TPi(_, a, b)) = S.NTerm(S.Lam (compress_term (a::G) (t, b))) (* GEN END FUN BRANCH *)

  fun (* GEN BEGIN FUN FIRST *) compress_kind G (NONE, S.KPi(_, a, k)) = S.KPi(S.MINUS, compress_type G (NONE, a), compress_kind (a::G) (NONE, k)) (* GEN END FUN FIRST *)
    | (* GEN BEGIN FUN BRANCH *) compress_kind G (SOME (m::ms), S.KPi(_, a, k)) = S.KPi(m, compress_type G (NONE, a), compress_kind (a::G) (SOME ms, k)) (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) compress_kind G (SOME [], S.Type) = S.Type (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) compress_kind G (NONE, S.Type) = S.Type (* GEN END FUN BRANCH *)


(* compress : cid * IntSyn.ConDec -> ConDec *)
  fun (* GEN BEGIN FUN FIRST *) compress (cid, IntSyn.ConDec (name, NONE, _, IntSyn.Normal, a, IntSyn.Type)) =
      let
          (* GEN BEGIN TAG OUTSIDE LET *) val x = xlate_type a (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val x = eta_expand_tp [] x (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val modes = Sgn.get_modes cid (* GEN END TAG OUTSIDE LET *)
      in
          Sgn.condec(name, compress_type [] (modes, x), x)
      end (* GEN END FUN FIRST *)
    | (* GEN BEGIN FUN BRANCH *) compress (cid, IntSyn.ConDec (name, NONE, _, IntSyn.Normal, k, IntSyn.Kind)) =
      let
          (* GEN BEGIN TAG OUTSIDE LET *) val x = xlate_kind k (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val modes = Sgn.get_modes cid (* GEN END TAG OUTSIDE LET *)
      in
          Sgn.tycondec(name, compress_kind [] (modes, x), x)
      end (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) compress (cid, IntSyn.ConDef (name, NONE, _, m, a, IntSyn.Type, _)) =
      let
          (* GEN BEGIN TAG OUTSIDE LET *) val m = xlate_term m (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val a = xlate_type a (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val astar = compress_type [] (NONE, a) (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val mstar = compress_term [] (m, a) (* GEN END TAG OUTSIDE LET *)
      in
          Sgn.defn(name, astar, a, mstar, m)
      end (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) compress (cid, IntSyn.ConDef (name, NONE, _, a, k, IntSyn.Kind, _)) =
      let
          (* GEN BEGIN TAG OUTSIDE LET *) val a = xlate_type a (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val k = xlate_kind k (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val kstar = compress_kind  [] (NONE, k) (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val astar = compress_type (Syntax.explodeKind kstar) (NONE, a) (* GEN END TAG OUTSIDE LET *)
      in
          Sgn.tydefn(name, kstar, k, astar, a)
      end (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) compress (cid, IntSyn.AbbrevDef (name, NONE, _, m, a, IntSyn.Type)) =
      let
          (* GEN BEGIN TAG OUTSIDE LET *) val m = xlate_term m (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val a = xlate_type a (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val astar = compress_type [] (NONE, a) (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val mstar = compress_term [] (m, a) (* GEN END TAG OUTSIDE LET *)
      in
          Sgn.abbrev(name, astar, a, mstar, m)
      end (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) compress (cid, IntSyn.AbbrevDef (name, NONE, _, a, k, IntSyn.Kind)) =
      let
          (* GEN BEGIN TAG OUTSIDE LET *) val a = xlate_type a (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val k = xlate_kind k (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val kstar = compress_kind  [] (NONE, k) (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val astar = compress_type (Syntax.explodeKind kstar) (NONE, a) (* GEN END TAG OUTSIDE LET *)
      in
          Sgn.tyabbrev(name, kstar, k, astar, a)
      end (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) compress _ = raise Unimp (* GEN END FUN BRANCH *)

  fun sgnLookup (cid) =
      let
          (* GEN BEGIN TAG OUTSIDE LET *) val c = Sgn.sub cid (* GEN END TAG OUTSIDE LET *)
      in
          case c of NONE =>
                    let
                        (* GEN BEGIN TAG OUTSIDE LET *) val c' = compress (cid, I.sgnLookup cid) (* GEN END TAG OUTSIDE LET *)
                        (* GEN BEGIN TAG OUTSIDE LET *) val _ = Sgn.update (cid, c') (* GEN END TAG OUTSIDE LET *)
                        (* GEN BEGIN TAG OUTSIDE LET *) val _ = print (Int.toString cid ^ "\n") (* GEN END TAG OUTSIDE LET *)
                    in
                        c'
                    end
                  | SOME x => x
      end

 (*  val sgnApp  = IntSyn.sgnApp

  fun sgnCompress () = sgnApp (ignore o sgnLookup) *)

  fun sgnCompressUpTo x = if x < 0 then () else (sgnCompressUpTo (x - 1); sgnLookup x; ())

  (* GEN BEGIN TAG OUTSIDE LET *) val check = Reductio.check (* GEN END TAG OUTSIDE LET *)

  fun extract f = ((f(); raise Match) handle Debug x => x)

  (* GEN BEGIN TAG OUTSIDE LET *) val set_modes = Sgn.set_modes (* GEN END TAG OUTSIDE LET *)

(* val log : Sgn.sigent list ref = ref [] *)


  (* given a cid, pick some vaguely plausible omission modes *)
  fun naiveModes cid =
      let
          (* GEN BEGIN TAG OUTSIDE LET *) val (ak, omitted_args, uni) =
              case I.sgnLookup cid of
                  I.ConDec(name, package, o_a, status, ak, uni) => (ak, o_a, uni)
                | I.ConDef(name, package, o_a, ak, def, uni, _) => (ak, o_a, uni)
                | I.AbbrevDef(name, package, o_a, ak, def, uni) => (ak, o_a, uni)
                | _ => raise NoModes (* GEN END TAG OUTSIDE LET *)
          fun (* GEN BEGIN FUN FIRST *) count_args (I.Pi(_, ak')) = 1 + count_args ak' (* GEN END FUN FIRST *)
            | (* GEN BEGIN FUN BRANCH *) count_args _ = 0 (* GEN END FUN BRANCH *)
          (* GEN BEGIN TAG OUTSIDE LET *) val total_args = count_args ak (* GEN END TAG OUTSIDE LET *)
  
          fun can_omit ms =
              let
                  (* GEN BEGIN TAG OUTSIDE LET *) val _ = Sgn.set_modes (cid, ms) (* GEN END TAG OUTSIDE LET *)
                  (* GEN BEGIN TAG OUTSIDE LET *) val s = compress (cid, I.sgnLookup cid) (* GEN END TAG OUTSIDE LET *)
                  (* GEN BEGIN TAG OUTSIDE LET *) val t = Sgn.typeOfSigent s (* GEN END TAG OUTSIDE LET *)
  (*                val _ = if true then log := !log @ [s] else () *)
                  (* GEN BEGIN TAG OUTSIDE LET *) val isValid = Reductio.check_plusconst_strictness t (* GEN END TAG OUTSIDE LET *)
  (*                val _ = if isValid then print "yup\n" else print "nope\n" *)
              in
                  isValid
              end
  
          fun (* GEN BEGIN FUN FIRST *) optimize' ms [] = rev ms (* GEN END FUN FIRST *)
            | (* GEN BEGIN FUN BRANCH *) optimize' ms (S.PLUS::ms') = if can_omit ((rev ms) @ (S.MINUS ::ms'))
                                           then optimize' (S.MINUS::ms) ms'
                                           else optimize' (S.PLUS::ms) ms' (* GEN END FUN BRANCH *)
            | (* GEN BEGIN FUN BRANCH *) optimize' ms (S.MINUS::ms') = if  can_omit ((rev ms) @ (S.OMIT :: ms'))
                                           then optimize' (S.OMIT::ms) ms'
                                           else optimize' (S.MINUS::ms) ms' (* GEN END FUN BRANCH *)
          fun optimize ms = optimize' [] ms
      in
          if uni = I.Kind
          then List.tabulate (total_args, ((* GEN BEGIN FUNCTION EXPRESSION *) fn _ => S.MINUS (* GEN END FUNCTION EXPRESSION *)))
          else optimize (List.tabulate (total_args, ((* GEN BEGIN FUNCTION EXPRESSION *) fn x => if x < omitted_args then S.MINUS else S.PLUS (* GEN END FUNCTION EXPRESSION *))))
      end


  (* Given a cid, return the "ideal" modes specified by twelf-
     omitted arguments. It is cheating to really use these for
     compression: the resulting signature will not typecheck. *)
  fun idealModes cid =
      let
          (* GEN BEGIN TAG OUTSIDE LET *) val (ak, omitted_args) =
              case I.sgnLookup cid of
                  I.ConDec(name, package, o_a, status, ak, uni) => (ak, o_a)
                | I.ConDef(name, package, o_a, ak, def, uni, _) => (ak, o_a)
                | I.AbbrevDef(name, package, o_a, ak, def, uni) => (ak, o_a)
                | _ => raise NoModes (* GEN END TAG OUTSIDE LET *)
          fun (* GEN BEGIN FUN FIRST *) count_args (I.Pi(_, ak')) = 1 + count_args ak' (* GEN END FUN FIRST *)
            | (* GEN BEGIN FUN BRANCH *) count_args _ = 0 (* GEN END FUN BRANCH *)
          (* GEN BEGIN TAG OUTSIDE LET *) val total_args = count_args ak (* GEN END TAG OUTSIDE LET *)
      in
          List.tabulate (total_args, ((* GEN BEGIN FUNCTION EXPRESSION *) fn x => if x < omitted_args then S.OMIT else S.MINUS (* GEN END FUNCTION EXPRESSION *)))
      end

(* not likely to work if the mode-setting function f actually depends on
   properties of earlier sgn entries *)
  fun setModesUpTo x f = if x < 0 then () else (setModesUpTo (x - 1) f;
                                                Sgn.set_modes (x, f x); ())

  fun sgnAutoCompress n f = (let
      (* GEN BEGIN TAG OUTSIDE LET *) val modes = f n (* GEN END TAG OUTSIDE LET *)
  in
      Sgn.set_modes(n, modes);
      Sgn.update (n, compress (n, IntSyn.sgnLookup n))
  end handle NoModes => ())

  fun sgnAutoCompressUpTo' n0 n f =
      if n0 > n
      then ()
      else let
              (* GEN BEGIN TAG OUTSIDE LET *) val _ =
                 (* has this entry already been processed? *)
                  case Sgn.sub n0
                   of SOME _ => ()
                    (* if not, compress it *)
                    | NONE =>
                      let
                          (* GEN BEGIN TAG OUTSIDE LET *) val modes = f n0 (* GEN END TAG OUTSIDE LET *)
                      in
                           (Sgn.set_modes(n0, modes);
                           Sgn.update (n0, compress (n0, IntSyn.sgnLookup n0));
                           if n0 mod 100 = 0 then print (Int.toString n0 ^ "\n") else ())
                      end handle NoModes => () (* GEN END TAG OUTSIDE LET *)
          in
              sgnAutoCompressUpTo' (n0 + 1) n f
          end
  fun sgnAutoCompressUpTo n f = sgnAutoCompressUpTo' 0 n f

  (* GEN BEGIN TAG OUTSIDE LET *) val check = Reductio.check (* GEN END TAG OUTSIDE LET *)

end (* GEN END FUNCTOR DECL *)

(*
c : ((o -> o) -> o -> o) -> o

a : o -> o

c ([x] a)

eta_expand_immediate ( a) ( o -> o)
*)
