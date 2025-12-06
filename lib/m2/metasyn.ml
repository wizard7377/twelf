(* Meta syntax *)
(* Author: Carsten Schuermann *)

let recctor MetaSyn ((*! module IntSyn' : INTSYN !*)
                 module Whnf : WHNF
                 (*! sharing Whnf.IntSyn = IntSyn' !*)
                   ): METASYN =
struct
  (*! module IntSyn = IntSyn' !*)

  exception Error of string

   type Var = int

  type mode =                       (* Mode                       *)
    Bot                                 (* M ::= Bot                  *)
  | Top                                 (*     | Top                  *)

  type prefix =                     (* Prefix P := *)
    Prefix of IntSyn.dctx               (* G   declarations           *)
            * Mode IntSyn.Ctx           (* Mtx modes                  *)
            * int IntSyn.Ctx            (* Btx splitting depths       *)

  type state =                      (* State S :=                 *)
    State of string                     (*             [name]         *)
             * Prefix                   (*             G; Mtx; Btx    *)
             * IntSyn.Exp               (*             |- V           *)

  type Sgn =                        (* Interface module type        *)
    SgnEmpty                            (* IS ::= .                   *)
  | ConDec of IntSyn.ConDec * Sgn       (*      | c:V, IS             *)

  local
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
    fun createEVarSpine (G, Vs) = createEVarSpineW (G, Whnf.whnf Vs)
    and createEVarSpineW (G, Vs as (I.Uni I.Type, s)) = (I.Nil, Vs) (* s = id *)
      | createEVarSpineW (G, Vs as (I.Root _, s)) = (I.Nil, Vs)   (* s = id *)
      | createEVarSpineW (G, (I.Pi ((D as I.Dec (_, V1), _), V2), s)) =
        let
          let X = I.newEVar (G, I.EClo (V1, s))
          let (S, Vs) = createEVarSpine (G, (V2, I.Dot (I.Exp (X), s)))
        in
          (I.App (X, S), Vs)
        end

    (* createAtomConst (G, c) = (U', (V', s'))

       Invariant:
       If   S |- c : Pi {V1 .. Vn}. V
       then . |- U' = c @ (Xn; .. Xn; Nil)
       and  . |- U' : V' [s']
    *)
    fun createAtomConst (G, H) =
      let
        let cid = (case H
                     of (I.Const cid) => cid
                      | (I.Skonst cid) => cid)
        let V = I.constType cid
        let (S, Vs) = createEVarSpine (G, (V, I.id))
      in
        (I.Root (H, S), Vs)
      end

    (* createAtomBVar (G, k) = (U', (V', s'))

       Invariant:
       If   G |- k : Pi {V1 .. Vn}. V
       then . |- U' = k @ (Xn; .. Xn; Nil)
       and  . |- U' : V' [s']
    *)
    fun createAtomBVar (G, k) =
      let
        let I.Dec (_, V) = I.ctxDec (G, k)
        let (S, Vs) = createEVarSpine (G, (V, I.id))
      in
        (I.Root (I.BVar (k), S), Vs)
      end

  in
    let createAtomConst = createAtomConst
    let createAtomBVar = createAtomBVar
  end

end (* functor MetaSyn *)







