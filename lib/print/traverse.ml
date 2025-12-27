open Basis

(* Generic Traversal Intended for_sml Language-Specific Printing *)

(* Author: Frank Pfenning *)

module type TRAVERSER = sig
  (* type kind *)
  type tp
  type obj
  type head
  type spine
  type dec
  type condec

  val atom : head * spine -> tp
  val arrow : tp * tp -> tp
  val pi : dec * tp -> tp
  val root : head * spine * tp -> obj

  (* propagate type to every root *)
  val lam : dec * obj -> obj
  val bvar : string -> head
  val const : string list * string -> head
  val def : string list * string -> head

  (* no evar, skonst, or fvar *)
  val nils : spine
  val app : obj * spine -> spine
  val dec : string * tp -> dec
  val objdec : string * tp -> condec
  (* val famdec : string * kind -> condec *)
  (* val objdef : string * obj * tp -> condec *)
  (* val famdef : string * tp * kind -> condec *)
  (* val skodec : string * tp -> condec *)
end

(* signature TRAVERSER *)

module type TRAVERSE = sig
  (*! structure IntSyn : Intsyn.INTSYN !*)
  module Traverser : TRAVERSER

  exception Error of string

  val fromConDec : IntSyn.conDec -> Traverser.condec option
  val const : string -> Traverser.condec
end

(* signature TRAVERSE *)
module Traverse
    (Whnf : Whnf.WHNF)
    (Names : Names.NAMES)
    (Traverser' : TRAVERSER) : TRAVERSE = struct
  (*! structure IntSyn = IntSyn' !*)

  module Traverser = Traverser'

  exception Error of string

  module I = IntSyn
  module T = Traverser
  (* from typecheck.fun *)

  (* inferCon (G, C) = V'

     Invariant:
     If    G |- C : V
     and  (C  doesn't contain FVars)
     then  G' |- V' : L      (for_sml some level L)
     and   G |- V = V' : L
     else exception Error is raised.
  *)

  let rec inferConW = function
    | G, I.BVar k' ->
        let (I.Dec (_, V)) = I.ctxDec (G, k') in
        Whnf.whnf (V, I.id)
    | G, I.Const c -> (I.constType c, I.id)
    | G, I.Def d -> (I.constType d, I.id)
  (* no case for_sml FVar, Skonst *)

  let rec fromHead = function
    | G, I.BVar n -> T.bvar (Names.bvarName (G, n))
    | G, I.Const cid ->
        let (Names.Qid (ids, id)) = Names.constQid cid in
        T.const (ids, id)
    | G, I.Def cid ->
        let (Names.Qid (ids, id)) = Names.constQid cid in
        T.def (ids, id)
    | _ -> raise (Error "Head not recognized")
  (* see also: print.fun *)

  let rec impCon = function
    | I.Const cid -> I.constImp cid
    | I.Def cid -> I.constImp cid
    | _ -> 0
  (* see also: print.fun *)

  (*
  fun dropImp (0, S) = S
    | dropImp (i, I.App (U, S)) = dropImp (i-1, S)
    | dropImp (i, I.SClo (S, s)) = I.SClo (dropImp (i, S), s)
    | dropImp _ = raise Error ("Missing implicit arguments")
  *)

  let rec fromTpW = function
    | G, (I.Root (C, S), s) ->
        T.atom
          (fromHead (G, C), fromSpine (impCon C, G, (S, s), inferConW (G, C)))
    | G, (I.Pi ((D, I.No), V2), s) ->
        T.arrow
          ( fromTp (G, (V1, s)),
            fromTp (I.Decl (G, I.decSub (D, s)), (V2, I.dot1 s)) )
    | G, (I.Pi ((D, I.Maybe), V2), s) ->
        let D' = Names.decUName (G, D) in
        T.pi
          ( fromDec (G, (D', s)),
            fromTp (I.Decl (G, I.decSub (D', s)), (V2, I.dot1 s)) )
    | _ -> raise (Error "Type not recognized")

  and fromTp (G, Vs) = fromTpW (G, Whnf.whnf Vs)

  and fromObjW = function
    | G, (I.Root (C, S), s), (V, t) ->
        T.root
          ( fromHead (G, C),
            fromSpine (impCon C, G, (S, s), inferConW (G, C)),
            fromTp (G, (V, t)) )
    | G, (I.Lam (D, U), s), (I.Pi (_, V), t) ->
        let D' = Names.decUName (G, D) in
        T.lam
          ( fromDec (G, (D', s)),
            fromObj (I.Decl (G, I.decSub (D', s)), (U, I.dot1 s), (V, I.dot1 t))
          )
    | _ -> raise (Error "Object not recognized")

  and fromObj (G, Us, Vt) = fromObjW (G, Whnf.whnf Us, Whnf.whnf Vt)

  and fromSpine = function
    | i, G, (I.Nil, s), Vt -> T.nils
    | i, G, (I.SClo (S, s'), s), Vt -> fromSpine (i, G, (S, I.comp (s', s)), Vt)
    | i, G, (I.App (U, S), s), (I.Pi ((I.Dec (_, V1), _), V2), t) ->
        if i > 0 (* drop implicit arg *) then
          fromSpine
            (i - 1, G, (S, s), Whnf.whnf (V2, I.Dot (I.Exp (I.EClo (U, s)), t)))
        else
          T.app
            ( fromObj (G, (U, s), (V1, t)),
              fromSpine
                (i, G, (S, s), Whnf.whnf (V2, I.Dot (I.Exp (I.EClo (U, s)), t)))
            )

  and fromDec (G, (I.Dec (Some x, V), s)) = T.dec (x, fromTp (G, (V, s)))
  (* NONE should not occur because of call to decName *)

  (*
    | fromDec (G, (I.Dec (NONE, V), s)) =
        T.dec ("_", fromTp (G, (V, s)))
    *)

  (* ignore a : K, d : A = M, b : K = A, and skolem constants *)

  let rec fromConDec = function
    | I.ConDec (c, parent, i, _, V, I.Type) ->
        Some (T.objdec (c, fromTp (I.Null, (V, I.id))))
    | _ -> None

  let fromConDec = fromConDec

  let rec const name =
    let qid =
      match Names.stringToQid name with
      | None -> raise (Error ("Malformed qualified identifier " ^ name))
      | Some qid -> qid
    in
    let cidOpt = Names.constLookup qid in
    let rec getConDec = function
      | None -> raise (Error ("Undeclared identifier " ^ Names.qidToString qid))
      | Some cid -> IntSyn.sgnLookup cid
    in
    let conDec = getConDec cidOpt in
    let _ = Names.varReset IntSyn.Null in
    let rec result = function
      | None -> raise (Error "Wrong kind of declaration")
      | Some r -> r
    in
    result (fromConDec conDec)
  (* local ... *)
end

(* functor Traverse *)
