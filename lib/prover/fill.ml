open Basis

(* Filling: Version 1.4 *)

(* Author: Carsten Schuermann *)

module type FILL = sig
  (*! structure IntSyn : Intsyn.INTSYN !*)
  (*! structure Tomega : Tomega.TOMEGA !*)
  module State : State.STATE

  exception Error of string

  type operator

  val expand : State.focus -> operator list
  val apply : operator -> unit
  val menu : operator -> string
end

(* signature FILL *)
(* Filling *)

(* Author: Carsten Schuermann *)

(* Date: Thu Mar 16 13:08:33 2006 *)

module Fill
    (Data : Data.DATA)
    (State' : State.STATE)
    (Abstract : Abstract.ABSTRACT)
    (TypeCheck : Typecheck.TYPECHECK)
    (Search : Search.SEARCH)
    (Whnf : Whnf.WHNF)
    (Unify : Unify.UNIFY) : FILL = struct
  (*! structure IntSyn = IntSyn' !*)

  (*! structure Tomega = Tomega' !*)

  module State = State'

  exception Error of string

  type operator =
    | FillWithConst of IntSyn.exp * IntSyn.cid
    | FillWithBVar of IntSyn.exp * int
  (* Representation Invariant:  FillWithBVar (X, n) :
           X is an evar GX |- X : VX
           GX |- n : W
           and VX and W are unifiable
       *)

  type operator = operator

  module S = State
  module T = Tomega
  module I = IntSyn

  exception Success of int
  (* expand' S = op'

       Invariant:
       If   |- S state
       then op' satifies representation invariant.
    *)

  let rec expand (S.FocusLF Y) =
    (* Y is lowered *)
    (* matchCtx (G, n, Fs) = Fs'

           Invariant:
           If G0 = G, G' and |G'| = n and Fs a list of filling operators that
           satisfy the representation invariant, then Fs' is a list of filling operators
           that satisfy the representation invariant.
        *)
    let rec try_ = function
      | Vs, Fs, O -> (
          try
            Cs.CSManager.trail (fun () ->
                Unify.unify (G, Vs, (V, I.id));
                O :: Fs)
          with Unify.Unify _ -> Fs)
      | (I.Pi ((I.Dec (_, V1), _), V2), s), Fs, O ->
          let X = I.newEVar (G, I.EClo (V1, s)) in
          try_ ((V2, I.Dot (I.Exp X, s)), Fs, O)
      | (I.EClo (V, s'), s), Fs, O -> try_ ((V, I.comp (s', s)), Fs, O)
    in
    let rec matchCtx = function
      | I.Null, _, Fs -> Fs
      | I.Decl (G, I.Dec (x, V)), n, Fs ->
          matchCtx
            (G, n + 1, try_ ((V, I.Shift (n + 1)), Fs, FillWithBVar (Y, n + 1)))
      | I.Decl (G, I.NDec _), n, Fs -> matchCtx (G, n + 1, Fs)
    in
    let rec matchSig = function
      | [], Fs -> Fs
      | I.Const c :: L, Fs ->
          matchSig (L, try_ ((I.constType c, I.id), Fs, FillWithConst (Y, c)))
    in
    matchCtx (G, 0, matchSig (Index.lookup (I.targetFam V), []))
  (* apply op = ()

       Invariant:
       If op is a filling operator that satisfies the representation invariant.
       The apply operation is guaranteed to always succeed.
    *)

  let rec apply = function
    | FillWithBVar (Y, n) ->
        (* Invariant : G |- s : G'   G' |- V : type *)
        let rec doit = function
          | Vs, k ->
              Unify.unify (G, Vs, (V, I.id));
              k I.Nil
          | (I.Pi ((I.Dec (_, V1), _), V2), s), k ->
              let X = I.newEVar (G, I.EClo (V1, s)) in
              doit ((V2, I.Dot (I.Exp X, s)), fun S -> k (I.App (X, S)))
          | (I.EClo (V, t), s), k -> doit ((V, I.comp (t, s)), k)
        in
        let (I.Dec (_, W)) = I.ctxDec (G, n) in
        doit
          ( (W, I.id),
            fun S -> Unify.unify (G, (Y, I.id), (I.Root (I.BVar n, S), I.id)) )
    | FillWithConst (Y, c) ->
        let rec doit = function
          | Vs, k ->
              Unify.unify (G0, Vs, (V, I.id));
              k I.Nil
          | (I.Pi ((I.Dec (_, V1), _), V2), s), k ->
              let X = I.newEVar (G0, I.EClo (V1, s)) in
              doit ((V2, I.Dot (I.Exp X, s)), fun S -> k (I.App (X, S)))
        in
        let W = I.constType c in
        doit
          ( (W, I.id),
            fun S -> Unify.unify (G0, (Y, I.id), (I.Root (I.Const c, S), I.id))
          )
  (* menu op = s'

       Invariant:
       If op is a filling operator
       then s' is a string describing the operation in plain text
    *)

  let rec menu = function
    | FillWithBVar (X, n) -> (
        match I.ctxLookup (Names.ctxName G, n) with
        | I.Dec (Some x, _) ->
            "Fill " ^ Names.evarName (G, X) ^ " with variable " ^ x)
    | FillWithConst (X, c) ->
        "Fill "
        ^ Names.evarName (G, X)
        ^ " with constant "
        ^ IntSyn.conDecName (IntSyn.sgnLookup c)

  let expand = expand
  let apply = apply
  let menu = menu
  (* local *)
end

(* functor Filling *)
