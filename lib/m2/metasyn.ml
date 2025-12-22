(* Meta syntax *)

(* Author: Carsten Schuermann *)

module type METASYN = sig
  (*! structure IntSyn : INTSYN !*)
  type mode = Bot | Top

  (*     | Top                  *)
  type prefix =
    | Prefix of
        IntSyn.dctx (* G   declarations           *)
        * mode IntSyn.ctx (* Mtx modes                  *)
        * int IntSyn.ctx

  (* Btx splitting depths       *)
  type state =
    | State of
        string (*             [name]         *)
        * prefix (*             G; Mtx; Btx    *)
        * IntSyn.exp

  (*             |- V           *)
  type sgn = SgnEmpty | ConDec of IntSyn.conDec * sgn

  (*      | c:V, IS             *)
  val createAtomConst : IntSyn.dctx * IntSyn.head -> IntSyn.exp * IntSyn.eclo
  val createAtomBVar : IntSyn.dctx * int -> IntSyn.exp * IntSyn.eclo
end

(* signature METASYN *)
(* Meta syntax *)

(* Author: Carsten Schuermann *)

module MetaSyn (Whnf : WHNF) : METASYN = struct
  (*! structure IntSyn = IntSyn' !*)

  exception Error of string

  type var = int
  type mode = Bot | Top
  (*     | Top                  *)

  type prefix =
    | Prefix of
        IntSyn.dctx (* G   declarations           *)
        * mode IntSyn.ctx (* Mtx modes                  *)
        * int IntSyn.ctx
  (* Btx splitting depths       *)

  type state =
    | State of
        string (*             [name]         *)
        * prefix (*             G; Mtx; Btx    *)
        * IntSyn.exp
  (*             |- V           *)

  type sgn = SgnEmpty | ConDec of IntSyn.conDec * sgn
  (*      | c:V, IS             *)

  module I = IntSyn
  (* createEVarSpineW (G, (V, s)) = ((V', s') , S')

       Invariant:
       If   G |- s : G1   and  G1 |- V = Pi {V1 .. Vn}. W : L
       and  G1, V1 .. Vn |- W atomic
       then G |- s' : G2  and  G2 |- V' : L
       and  S = X1; ...; Xn; Nil
       and  G |- W [1.2...n. s o ^n] = V' [s']
       and  G |- S : V [s] >  V' [s']
    *)

  let rec createEVarSpine (G, Vs) = createEVarSpineW (G, Whnf.whnf Vs)

  and createEVarSpineW = function
    | G, Vs -> (I.Nil, Vs)
    | G, Vs -> (I.Nil, Vs)
    | G, (I.Pi ((D, _), V2), s) ->
        let X = I.newEVar (G, I.EClo (V1, s)) in
        let S, Vs = createEVarSpine (G, (V2, I.Dot (I.Exp X, s))) in
        (I.App (X, S), Vs)
  (* createAtomConst (G, c) = (U', (V', s'))

       Invariant:
       If   S |- c : Pi {V1 .. Vn}. V
       then . |- U' = c @ (Xn; .. Xn; Nil)
       and  . |- U' : V' [s']
    *)

  let rec createAtomConst (G, H) =
    let cid = match H with I.Const cid -> cid | I.Skonst cid -> cid in
    let V = I.constType cid in
    let S, Vs = createEVarSpine (G, (V, I.id)) in
    (I.Root (H, S), Vs)
  (* createAtomBVar (G, k) = (U', (V', s'))

       Invariant:
       If   G |- k : Pi {V1 .. Vn}. V
       then . |- U' = k @ (Xn; .. Xn; Nil)
       and  . |- U' : V' [s']
    *)

  let rec createAtomBVar (G, k) =
    let (I.Dec (_, V)) = I.ctxDec (G, k) in
    let S, Vs = createEVarSpine (G, (V, I.id)) in
    (I.Root (I.BVar k, S), Vs)

  let createAtomConst = createAtomConst
  let createAtomBVar = createAtomBVar
end

(* functor MetaSyn *)
