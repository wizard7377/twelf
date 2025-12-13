(* Meta syntax *)
(* Author: Carsten Schuermann *)

functor (* GEN BEGIN FUNCTOR DECL *) MetaSyn ((*! structure IntSyn' : INTSYN !*)
                 structure Whnf : WHNF
                 (*! sharing Whnf.IntSyn = IntSyn' !*)
                   )
  : METASYN =
struct
  (*! structure IntSyn = IntSyn' !*)

  exception Error of string

   type var = int

  datatype mode =                       (* Mode                       *)
    Bot                                 (* M ::= Bot                  *)
  | Top                                 (*     | Top                  *)

  datatype prefix =                     (* Prefix P := *)
    Prefix of IntSyn.dctx               (* G   declarations           *)
            * mode IntSyn.ctx           (* Mtx modes                  *)
            * int IntSyn.ctx            (* Btx splitting depths       *)

  datatype state =                      (* State S :=                 *)
    State of string                     (*             [name]         *)
             * prefix                   (*             G; Mtx; Btx    *)
             * IntSyn.exp               (*             |- V           *)

  datatype sgn =                        (* Interface signature        *)
    SgnEmpty                            (* IS ::= .                   *)
  | ConDec of IntSyn.con_dec * sgn       (*      | c:V, IS             *)

  local
    structure I = IntSyn

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
    and (* GEN BEGIN FUN FIRST *) createEVarSpineW (G, Vs as (I.Uni I.Type, s)) = (I.Nil, Vs) (* GEN END FUN FIRST *) (* s = id *)
      | (* GEN BEGIN FUN BRANCH *) createEVarSpineW (G, Vs as (I.Root _, s)) = (I.Nil, Vs) (* GEN END FUN BRANCH *)   (* s = id *)
      | (* GEN BEGIN FUN BRANCH *) createEVarSpineW (G, (I.Pi ((D as I.Dec (_, V1), _), V2), s)) =
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val X = I.newEVar (G, I.EClo (V1, s)) (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val (S, Vs) = createEVarSpine (G, (V2, I.Dot (I.Exp (X), s))) (* GEN END TAG OUTSIDE LET *)
        in
          (I.App (X, S), Vs)
        end (* GEN END FUN BRANCH *)

    (* createAtomConst (G, c) = (U', (V', s'))

       Invariant:
       If   S |- c : Pi {V1 .. Vn}. V
       then . |- U' = c @ (Xn; .. Xn; Nil)
       and  . |- U' : V' [s']
    *)
    fun createAtomConst (G, H) =
      let
        (* GEN BEGIN TAG OUTSIDE LET *) val cid = (case H
                     of (I.Const cid) => cid
                      | (I.Skonst cid) => cid) (* GEN END TAG OUTSIDE LET *)
        (* GEN BEGIN TAG OUTSIDE LET *) val V = I.constType cid (* GEN END TAG OUTSIDE LET *)
        (* GEN BEGIN TAG OUTSIDE LET *) val (S, Vs) = createEVarSpine (G, (V, I.id)) (* GEN END TAG OUTSIDE LET *)
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
        (* GEN BEGIN TAG OUTSIDE LET *) val I.Dec (_, V) = I.ctxDec (G, k) (* GEN END TAG OUTSIDE LET *)
        (* GEN BEGIN TAG OUTSIDE LET *) val (S, Vs) = createEVarSpine (G, (V, I.id)) (* GEN END TAG OUTSIDE LET *)
      in
        (I.Root (I.BVar (k), S), Vs)
      end

  in
    (* GEN BEGIN TAG OUTSIDE LET *) val createAtomConst = createAtomConst (* GEN END TAG OUTSIDE LET *)
    (* GEN BEGIN TAG OUTSIDE LET *) val createAtomBVar = createAtomBVar (* GEN END TAG OUTSIDE LET *)
  end

end (* GEN END FUNCTOR DECL *) (* functor MetaSyn *)







