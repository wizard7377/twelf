open Basis
(* Theorems *)

(* Author: Carsten Schuermann *)

(* Modified: Brigitte Pientka *)

module type THMSYN = sig
  module Names : Names.NAMES

  exception Error of string

  (*! type Param = string option !*)
  type order = Varg of string list | Lex of order list | Simul of order list

  (* -bp *)
  type predicate = Less | Leq | Eq
  type redOrder = RedOrder of predicate * order * order
  type callpats = Callpats of IntSyn.cid * string option list list

  (* Termination declaration *)
  type tDecl = TDecl of order * callpats

  (* -bp *)
  (* Reduction declaration *)
  type rDecl = RDecl of (redOrder * callpats)

  (* Tabled declaration *)
  type tabledDecl = TabledDecl of IntSyn.cid

  (* KeepTable declaration *)
  type keepTableDecl = KeepTableDecl of IntSyn.cid

  (* Theorem declaration  *)
  type thDecl =
    | ThDecl of
        IntSyn.dec IntSyn.ctx
        * IntSyn.dec IntSyn.ctx list
        * IntSyn.dec IntSyn.ctx
        * ModeSyn.mode IntSyn.ctx
        * int

  (* Proof declaration *)
  type pDecl = PDecl of int * tDecl

  (* World declaration *)
  (*  datatype WDecl = 
    WDecl of (IntSyn.Dec IntSyn.Ctx * 
	      IntSyn.Dec IntSyn.Ctx) list * Callpats
*)
  type wDecl = WDecl of Names.qid list * callpats

  val theoremDecToConDec :
    (string * thDecl) * Paths.region ->
    IntSyn.dec IntSyn.ctx * IntSyn.dec IntSyn.ctx list * IntSyn.conDec

  val theoremDecToModeSpine :
    (string * thDecl) * Paths.region -> ModeSyn.modeSpine
end

(* signature THMSYN *)
(* Theorems *)

(* Author: Carsten Schuermann *)

(* Modified: Brigitte Pientka *)

module ThmSyn
    (Abstract : Abstract.ABSTRACT)
    (Whnf : Whnf.WHNF)
    (Names' : Names.NAMES) : THMSYN = struct
  (*! structure IntSyn = IntSyn !*)

  (*! structure ModeSyn = ModeSyn' *)

  (*! structure Paths = Paths' !*)

  module Names = Names'

  exception Error of string

  let rec error (r, msg) = raise (Error (Paths.wrap (r, msg)))

  type param = string option
  type order = Varg of string list | Lex of order list | Simul of order list
  (* -bp *)

  type predicate = Less | Leq | Eq
  type redOrder = RedOrder of predicate * order * order
  type callpats = Callpats of IntSyn.cid * param list list
  (* Termination declaration *)

  type tDecl = TDecl of (order * callpats)
  (* -bp *)

  (* Reduction declaration *)

  type rDecl = RDecl of (redOrder * callpats)
  (* Tabled declaration *)

  type tabledDecl = TabledDecl of IntSyn.cid
  (* KeepTable declaration *)

  type keepTableDecl = KeepTableDecl of IntSyn.cid
  (* Theorem declaration *)

  type thDecl =
    | ThDecl of
        IntSyn.dec IntSyn.ctx
        * IntSyn.dec IntSyn.ctx list
        * IntSyn.dec IntSyn.ctx
        * ModeSyn.mode IntSyn.ctx
        * int
  (* Proof declaration *)

  type pDecl = PDecl of int * tDecl
  (* World declaration *)

  (*  datatype WDecl =
    WDecl of (IntSyn.Dec IntSyn.Ctx *
              IntSyn.Dec IntSyn.Ctx) list * Callpats *)

  type wDecl = WDecl of Names.qid list * callpats

  module I = IntSyn
  module M = ModeSyn
  (* theoremDecToConDec (name, T) = D'

       Invariant:
       If   name is the name of a theorem
       and  T is the declaration of a theorem
       then D' is a constant type declaration of this theorem
    *)

  let rec theoremDecToConDec ((name, ThDecl (GBs, G, MG, i)), r) =
    (* theoremToConDec' G V = V'

             Invariant:
             If   G = V1 .. Vn
             and  G |- V : kind
             then V' = {V1} .. {Vn} V
             and  . |-  V' : kind
          *)
    let rec theoremToConDec' = function
      | I.Null, V -> V
      | I.Decl (G, D), V ->
          if Abstract.closedDec (G, (D, I.id)) then
            theoremToConDec'
              (G, Abstract.piDepend ((Whnf.normalizeDec (D, I.id), I.Maybe), V))
          else error (r, "Free variables in theorem declaration")
    in
    ( GBs,
      I.ConDec
        (name, None, i, I.Normal, theoremToConDec' (G, I.Uni I.Type), I.Kind) )
  (* theoremDecToModeSpine (name, T) = mS'

       Invariant:
       If   name is the name of a theorem
       and  T is the declaration of a theorem
       then mS' is a mode spine reflecting the
         quantifier information for_sml the theorem
    *)

  let rec theoremDecToModeSpine ((name, ThDecl (GBs, G, MG, i)), r) =
    let rec theoremToModeSpine' = function
      | I.Null, I.Null, mS -> mS
      | I.Decl (G, I.Dec (x, _)), I.Decl (MG, m), mS ->
          theoremToModeSpine' (G, MG, M.Mapp (M.Marg (m, x), mS))
    in
    theoremToModeSpine' (G, MG, M.Mnil)

  let theoremDecToConDec = theoremDecToConDec
  let theoremDecToModeSpine = theoremDecToModeSpine
  (* local *)
end

(* functor ThmSyn *)
