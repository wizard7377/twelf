module Compress (Global : GLOBAL) =
struct

  module I = IntSyn
  module S = Syntax
  module Sgn = Sgn

  exception Unimp
  exception NoModes (* modes are not appropriate for the given I.ConDec *)

  let debug = ref ~1

  let rec sgnReset () = Sgn.clear ()

(* xlate_type : IntSyn.exp -> Syntax.tp *)
  let rec xlate_type = function (I.Pi ((I.Dec(_, e1), _), e2)) -> S.TPi(S.MINUS, xlate_type e1, xlate_type e2)
    | (I.Root (I.Const cid, sp)) -> S.TRoot(cid, xlate_spine sp)
    | (I.Root (I.Def cid, sp)) -> S.TRoot(cid, xlate_spine sp) (* assuming cids of consts and defs to be disjoint *)
    | (I.Root (I.NSDef cid, sp)) -> S.TRoot(cid, xlate_spine sp)  (* ditto *)
    | (I.Lam (_, t)) -> xlate_type t  (* for type definitions, simply strip off the lambdas and leave
                                                   the variables free*)
  and xlate_spine I.Nil = []
    | xlate_spine (I.App(e, s)) = xlate_spinelt e :: xlate_spine s
  and xlate_spinelt e  = S.Elt(xlate_term e)
  and xlate_term (I.Root (I.Const cid, sp)) = S.ATerm(S.ARoot(S.Const cid, xlate_spine sp))
    | xlate_term (I.Root (I.Def cid, sp)) = S.ATerm(S.ARoot(S.Const cid, xlate_spine sp)) (* assuming cids of consts and defs to be disjoint *)
    | xlate_term (I.Root (I.NSDef cid, sp)) = S.ATerm(S.ARoot(S.Const cid, xlate_spine sp)) (* ditto *)
    | xlate_term (I.Root (I.BVar vid, sp)) = S.ATerm(S.ARoot(S.Var (vid - 1), xlate_spine sp))
    | xlate_term (I.Lam (_, e)) = S.NTerm(S.Lam (xlate_term e))
(* xlate_kind : IntSyn.exp -> Syntax.knd *)
  let rec xlate_kind = function (I.Pi ((I.Dec(_, e1), _), e2)) -> S.KPi(S.MINUS, xlate_type e1, xlate_kind e2)
    | (I.Uni(I.Type)) -> S.Type

  local open Syntax in
  (* simple skeletal form of types
     omits all dependencies, type constants *)
  type simple_tp = Base | Arrow of simple_tp * simple_tp

  let rec simplify_tp = function (TPi (_, t1, t2)) -> Arrow(simplify_tp t1, simplify_tp t2)
    | (TRoot _) -> Base
  let rec simplify_knd = function (KPi (_, t1, k2)) -> Arrow(simplify_tp t1, simplify_knd k2)
    | (Type) -> Base

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
  let rec eta_expand_term = function G (NTerm t) T -> NTerm(eta_expand_nterm G t T)
    | G (ATerm t) T -> ATerm(eta_expand_aterm G t)
  and eta_expand_nterm G (Lam t) (Arrow(t1, t2)) = Lam(eta_expand_term (t1::G) t t2)
    | eta_expand_nterm G (NRoot (h,s)) T = NRoot(h, eta_expand_spine G s T)
    | eta_expand_nterm G (Lam t) Base = raise Syntax "Lambda occurred where term of base type expected"
  and eta_expand_aterm G (ARoot (Const n, s)) =
      let
          let stp = simplify_tp(typeOf (Sgn.o_classifier n))
      in
          ARoot(Const n, eta_expand_spine G s stp)
      end
    | eta_expand_aterm G (ARoot (Var n, s)) =
      let
          let stp = List.nth(G, n)
      in
          ARoot(Var n, eta_expand_var_spine G s stp)
      end
    | eta_expand_aterm G (ERoot _) = raise Syntax "invariant violated in eta_expand_aterm"
  and eta_expand_tp G (TRoot(n, s)) =
      let
          let stp = simplify_knd(kindOf (Sgn.o_classifier n))
      in
          TRoot(n, eta_expand_spine G s stp)
      end
    | eta_expand_tp G (TPi(m,a,b)) = TPi(m,eta_expand_tp G a, eta_expand_tp (simplify_tp a::G) b)
  and eta_expand_knd G (Type) = Type
    | eta_expand_knd G (KPi(m,a,b)) = KPi(m,eta_expand_tp G a, eta_expand_knd (simplify_tp a::G) b)
  and eta_expand_spine G [] Base = [] (* this seems risky, but okay as long as the only eta-shortness we find is in variable-headed pattern spines *)
    | eta_expand_spine G ((Elt m)::tl) (Arrow(t1, t2)) =
      Elt(eta_expand_term G m t1) :: eta_expand_spine G tl t2
    | eta_expand_spine G ((AElt m)::tl) (Arrow(t1, t2)) =
      AElt(eta_expand_aterm G m) :: eta_expand_spine G tl t2
    | eta_expand_spine G ((Ascribe(m,a))::tl) (Arrow(t1, t2)) =
      Ascribe(eta_expand_nterm G m t1, eta_expand_tp G a) :: eta_expand_spine G tl t2
    | eta_expand_spine G (Omit::tl) (Arrow(t1,t2)) =
      Omit :: eta_expand_spine G tl t2
    | eta_expand_spine _ _ _ = raise Syntax "Can't figure out how to eta expand spine"
  (* the behavior here is that we are eta-expanding all of the elements of the spine, not the head of *this* spine *)
  and eta_expand_var_spine G [] _ = [] (* in fact this spine may not be eta-long yet *)
    | eta_expand_var_spine G ((Elt m)::tl) (Arrow(t1, t2)) =
      Elt(eta_expand_immediate (eta_expand_term G m t1, t1)) :: eta_expand_spine G tl t2
    | eta_expand_var_spine _ _ _ = raise Syntax "Can't figure out how to eta expand var-headed spine"
  (* here's where the actual expansion takes place *)
  and eta_expand_immediate (m, Base) = m
    | eta_expand_immediate (NTerm(Lam m), Arrow(t1, t2)) =
      NTerm(Lam(eta_expand_immediate(m, t2)))
    | eta_expand_immediate (m, Arrow(t1, t2)) =
      let
          let variable = eta_expand_immediate(ATerm(ARoot(Var 0, [])), t1)
      in
          NTerm(Lam(eta_expand_immediate(apply_to(shift m, variable), t2)))
      end
  and apply_to (ATerm(ARoot(h, s)), m) = ATerm(ARoot(h, s @ [Elt m]))
    | apply_to (NTerm(NRoot(h, s)), m) = NTerm(NRoot(h, s @ [Elt m]))
    | apply_to _ = raise Syntax "Invariant violated in apply_to"
  end

  let typeOf = S.typeOf
  let kindOf = S.kindOf

  exception Debug of S.spine * S.tp * S.tp
 (* let compress_type : Syntax.tp list -> Syntax.mode list option * Syntax.tp -> Syntax.tp *)
 (* the length of the mode list, if there is one, should correspond to the number of pis in the input type.
    however, as indicated in the XXX comment below, it seems necessary to treat SOME of empty list
    as if it were NONE. This doesn't seem right. *)
  let rec compress_type G s = (* if !debug < 0
                          then *) compress_type' G s
                          (* else  (if !debug = 0 then raise Debug(G, s) else ();
                                debug := !debug - 1; compress_type' G s) *)
  and compress_type' G (NONE, S.TPi(_, a, b)) = S.TPi(S.MINUS, compress_type G (NONE, a), compress_type (a::G) (NONE, b))
    | compress_type' G (SOME (m::ms), S.TPi(_, a, b)) = S.TPi(m, compress_type G (NONE, a), compress_type (a::G) (SOME ms, b))
    | compress_type' G (SOME [], S.TRoot(cid, sp)) = S.TRoot(cid, compress_type_spine G (sp,
                                                                                   kindOf(Sgn.o_classifier cid),
                                                                                   kindOf(Sgn.classifier cid)))
    | compress_type' G (NONE, a as S.TRoot _) = compress_type G (SOME [], a)
    | compress_type' G (SOME [], a as S.TPi _) = compress_type G (NONE, a) (* XXX sketchy *)

(* XXX: optimization: don't compute mstar if omit? *)
  and compress_type_spine G ([], w, wstar) = []
    | compress_type_spine G ((S.Elt m)::sp, S.KPi(_, a, v), S.KPi(mode, astar, vstar)) =
      let
          let mstar = compress_term G (m, a)
          let sstar = compress_type_spine G (sp,
                                        S.subst_knd (S.TermDot(m, a, S.Id)) v,
                                        S.subst_knd (S.TermDot(mstar, astar, S.Id)) vstar)
      in
          case (mode, mstar) of
              (S.OMIT, _) => S.Omit::sstar
            | (S.MINUS, _) => S.Elt mstar::sstar
            | (S.PLUS, S.ATerm t) => S.AElt t::sstar
            | (S.PLUS, S.NTerm t) => S.Ascribe(t, compress_type G (NONE, a))::sstar
      end
  and compress_spine G ([], w, wstar) = []
    | compress_spine G ((S.Elt m)::sp, S.TPi(_, a, v), S.TPi(mode, astar, vstar)) =
      let
          let mstar = compress_term G (m, a)
          let sstar = compress_spine G (sp,
                                        S.subst_tp (S.TermDot(m, a, S.Id)) v,
                                        S.subst_tp (S.TermDot(mstar, astar, S.Id)) vstar)
      in
          case (mode, mstar) of
              (S.OMIT, _) => S.Omit::sstar
            | (S.MINUS, _) => S.Elt mstar::sstar
            | (S.PLUS, S.ATerm t) => S.AElt t::sstar
            | (S.PLUS, S.NTerm t) => S.Ascribe(t, compress_type G (NONE, a))::sstar
      end
  and compress_term G (S.ATerm(S.ARoot(S.Var n, sp)), _) =
      let
          let a = S.ctxLookup(G, n)
          let astar = compress_type G (NONE, a)
      in
          S.ATerm(S.ARoot(S.Var n, compress_spine G (sp, a, astar)))
      end
    | compress_term G (S.ATerm(S.ARoot(S.Const n, sp)), _) =
      let
          let a = typeOf (Sgn.o_classifier n)
          let astar = typeOf (Sgn.classifier n)
          let term_former = case Sgn.get_p n of
                                SOME false => S.NTerm o S.NRoot
                              | _ => S.ATerm o S.ARoot
      in
          term_former(S.Const n, compress_spine G (sp, a, astar))
      end
    | compress_term G (S.NTerm(S.Lam t),S.TPi(_, a, b)) = S.NTerm(S.Lam (compress_term (a::G) (t, b)))

  let rec compress_kind = function G (NONE, S.KPi(_, a, k)) -> S.KPi(S.MINUS, compress_type G (NONE, a), compress_kind (a::G) (NONE, k))
    | G (SOME (m::ms), S.KPi(_, a, k)) -> S.KPi(m, compress_type G (NONE, a), compress_kind (a::G) (SOME ms, k))
    | G (SOME [], S.Type) -> S.Type
    | G (NONE, S.Type) -> S.Type


(* compress : cid * IntSyn.ConDec -> ConDec *)
  let rec compress = function (cid, IntSyn.ConDec (name, NONE, _, IntSyn.Normal, a, IntSyn.Type)) -> 
      let
          let x = xlate_type a
          let x = eta_expand_tp [] x
          let modes = Sgn.get_modes cid
      in
          Sgn.condec(name, compress_type [] (modes, x), x)
      end
    | (cid, IntSyn.ConDec (name, NONE, _, IntSyn.Normal, k, IntSyn.Kind)) -> 
      let
          let x = xlate_kind k
          let modes = Sgn.get_modes cid
      in
          Sgn.tycondec(name, compress_kind [] (modes, x), x)
      end
    | (cid, IntSyn.ConDef (name, NONE, _, m, a, IntSyn.Type, _)) -> 
      let
          let m = xlate_term m
          let a = xlate_type a
          let astar = compress_type [] (NONE, a)
          let mstar = compress_term [] (m, a)
      in
          Sgn.defn(name, astar, a, mstar, m)
      end
    | (cid, IntSyn.ConDef (name, NONE, _, a, k, IntSyn.Kind, _)) -> 
      let
          let a = xlate_type a
          let k = xlate_kind k
          let kstar = compress_kind  [] (NONE, k)
          let astar = compress_type (Syntax.explodeKind kstar) (NONE, a)
      in
          Sgn.tydefn(name, kstar, k, astar, a)
      end
    | (cid, IntSyn.AbbrevDef (name, NONE, _, m, a, IntSyn.Type)) -> 
      let
          let m = xlate_term m
          let a = xlate_type a
          let astar = compress_type [] (NONE, a)
          let mstar = compress_term [] (m, a)
      in
          Sgn.abbrev(name, astar, a, mstar, m)
      end
    | (cid, IntSyn.AbbrevDef (name, NONE, _, a, k, IntSyn.Kind)) -> 
      let
          let a = xlate_type a
          let k = xlate_kind k
          let kstar = compress_kind  [] (NONE, k)
          let astar = compress_type (Syntax.explodeKind kstar) (NONE, a)
      in
          Sgn.tyabbrev(name, kstar, k, astar, a)
      end
    | _ -> raise Unimp

  let rec sgnLookup (cid) =
      let
          let c = Sgn.sub cid
      in
          case c of NONE =>
                    let
                        let c' = compress (cid, I.sgnLookup cid)
                        let _ = Sgn.update (cid, c')
                        let _ = print (Int.toString cid ^ "\n")
                    in
                        c'
                    end
                  | SOME x => x
      end

 (*  let sgnApp  = IntSyn.sgnApp

  let rec sgnCompress () = sgnApp (ignore o sgnLookup) *)

  let rec sgnCompressUpTo x = if x < 0 then () else (sgnCompressUpTo (x - 1); sgnLookup x; ())

  let check = Reductio.check

  let rec extract f = ((f(); raise Match) handle Debug x => x)

  let set_modes = Sgn.set_modes

(* let log : Sgn.sigent list ref = ref [] *)


  (* given a cid, pick some vaguely plausible omission modes *)
  let rec naiveModes cid =
      let
          let (ak, omitted_args, uni) =
              case I.sgnLookup cid of
                  I.ConDec(name, package, o_a, status, ak, uni) => (ak, o_a, uni)
                | I.ConDef(name, package, o_a, ak, def, uni, _) => (ak, o_a, uni)
                | I.AbbrevDef(name, package, o_a, ak, def, uni) => (ak, o_a, uni)
                | _ => raise NoModes
          let rec count_args = function (I.Pi(_, ak')) -> 1 + count_args ak'
            | _ -> 0
          let total_args = count_args ak

          let rec can_omit ms =
              let
                  let _ = Sgn.set_modes (cid, ms)
                  let s = compress (cid, I.sgnLookup cid)
                  let t = Sgn.typeOfSigent s
(*                let _ = if true then log := !log @ [s] else () *)
                  let isValid = Reductio.check_plusconst_strictness t
(*                let _ = if isValid then print "yup\n" else print "nope\n" *)
              in
                  isValid
              end

          let rec optimize' = function ms [] -> rev ms
            | ms (S.PLUS::ms') -> if can_omit ((rev ms) @ (S.MINUS ::ms'))
                                           then optimize' (S.MINUS::ms) ms'
                                           else optimize' (S.PLUS::ms) ms'
            | ms (S.MINUS::ms') -> if  can_omit ((rev ms) @ (S.OMIT :: ms'))
                                           then optimize' (S.OMIT::ms) ms'
                                           else optimize' (S.MINUS::ms) ms'
          let rec optimize ms = optimize' [] ms
      in
          if uni = I.Kind
          then List.tabulate (total_args, (fun _ -> S.MINUS))
          else optimize (List.tabulate (total_args, (fun x -> if x < omitted_args then S.MINUS else S.PLUS)))
      end


  (* Given a cid, return the "ideal" modes specified by twelf-
     omitted arguments. It is cheating to really use these for
     compression: the resulting module type will not typecheck. *)
  let rec idealModes cid =
      let
          let (ak, omitted_args) =
              case I.sgnLookup cid of
                  I.ConDec(name, package, o_a, status, ak, uni) => (ak, o_a)
                | I.ConDef(name, package, o_a, ak, def, uni, _) => (ak, o_a)
                | I.AbbrevDef(name, package, o_a, ak, def, uni) => (ak, o_a)
                | _ => raise NoModes
          let rec count_args = function (I.Pi(_, ak')) -> 1 + count_args ak'
            | _ -> 0
          let total_args = count_args ak
      in
          List.tabulate (total_args, (fun x -> if x < omitted_args then S.OMIT else S.MINUS))
      end

(* not likely to work if the mode-setting function f actually depends on
   properties of earlier sgn entries *)
  let rec setModesUpTo x f = if x < 0 then () else (setModesUpTo (x - 1) f;
                                                Sgn.set_modes (x, f x); ())

  let rec sgnAutoCompress n f = (let
      let modes = f n
  in
      Sgn.set_modes(n, modes);
      Sgn.update (n, compress (n, IntSyn.sgnLookup n))
  end handle NoModes => ())

  let rec sgnAutoCompressUpTo' n0 n f =
      if n0 > n
      then ()
      else let
              let _ =
                 (* has this entry already been processed? *)
                  case Sgn.sub n0
                   of SOME _ => ()
                    (* if not, compress it *)
                    | NONE =>
                      let
                          let modes = f n0
                      in
                           (Sgn.set_modes(n0, modes);
                           Sgn.update (n0, compress (n0, IntSyn.sgnLookup n0));
                           if n0 mod 100 = 0 then print (Int.toString n0 ^ "\n") else ())
                      end handle NoModes => ()
          in
              sgnAutoCompressUpTo' (n0 + 1) n f
          end
  let rec sgnAutoCompressUpTo n f = sgnAutoCompressUpTo' 0 n f

  let check = Reductio.check

end

(*
c : ((o -> o) -> o -> o) -> o

a : o -> o

c ([x] a)

eta_expand_immediate ( a) ( o -> o)
*)
