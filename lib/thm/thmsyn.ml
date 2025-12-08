(* Theorems *)
(* Author: Carsten Schuermann *)
(* Modified: Brigitte Pientka *)

module ThmSyn ((*! (IntSyn : INTSYN) !*)
                (*! module ModeSyn' : MODESYN !*)
                (*! sharing ModeSyn'.IntSyn = IntSyn !*)
                (Abstract : ABSTRACT)
                (*! sharing Abstract.IntSyn = IntSyn !*)
                (Whnf : WHNF)
                (*! sharing Whnf.IntSyn = IntSyn !*)
                (*! module Paths' : PATHS !*)
                module Names' : NAMES): THMSYN =
                (*! sharing Names'.IntSyn = IntSyn !*)
struct
  (*! module IntSyn = IntSyn !*)
  (*! module ModeSyn = ModeSyn' *)
  (*! module Paths = Paths' !*)
  module Names = Names'

  exception Error of string
  fun error (r, msg) = raise Error (Paths.wrap (r, msg))


  type param = string option

  type order =
    Varg of string list
  | Lex of order list
  | Simul of order list

  (* -bp *)
  type predicate = Less | Leq | Eq

  type redOrder =
      RedOrder of predicate * order * order

  type callpats =
    Callpats of (IntSyn.cid * Param list) list

  (* Termination declaration *)
  type tDecl =
    TDecl of (order * callpats)

  (* -bp *)
  (* Reduction declaration *)
  type rDecl =
    RDecl of (redOrder * callpats)

  (* Tabled declaration *)
  type tabledDecl =
    TabledDecl of IntSyn.cid

  (* KeepTable declaration *)
  type keepTableDecl =
    KeepTableDecl of IntSyn.cid

  (* Theorem declaration *)
  type thDecl =
    ThDecl of (IntSyn.Dec IntSyn.ctx * IntSyn.Dec IntSyn.ctx) list
              * IntSyn.Dec IntSyn.ctx * ModeSyn.Mode IntSyn.ctx * int

  (* Proof declaration *)
  type pDecl =
    PDecl of int * tDecl

  (* World declaration *)
(*  type WDecl =
    WDecl of (IntSyn.Dec IntSyn.ctx *
              IntSyn.Dec IntSyn.ctx) list * Callpats *)
  type wDecl =
    WDecl of Names.Qid list * callpats

  local

    module I = IntSyn
    module M = ModeSyn

    (* theoremDecToConDec (name, T) = D'

       Invariant:
       If   name is the name of a theorem
       and  T is the declaration of a theorem
       then D' is a constant type declaration of this theorem
    *)

    fun theoremDecToConDec ((name, ThDecl (GBs, G, MG, i)), r) =
        let
          (* theoremToConDec' G V = V'

             Invariant:
             If   G = V1 .. Vn
             and  G |- V : kind
             then V' = {V1} .. {Vn} V
             and  . |-  V' : kind
          *)

          fun theoremToConDec' (I.Null, V) = V
            | theoremToConDec' (I.Decl (G, D), V) =
                if Abstract.closedDec (G, (D, I.id))
                  then theoremToConDec' (G, Abstract.piDepend ((Whnf.normalizeDec (D, I.id),
                                                                I.Maybe), V))
                else error (r, "Free variables in theorem declaration")
        in
          (GBs, I.ConDec (name, NONE, i, I.Normal, theoremToConDec' (G, I.Uni (I.Type)), I.Kind))
        end


    (* theoremDecToModeSpine (name, T) = mS'

       Invariant:
       If   name is the name of a theorem
       and  T is the declaration of a theorem
       then mS' is a mode spine reflecting the
         quantifier information for the theorem
    *)

    fun theoremDecToModeSpine ((name,  ThDecl (GBs, G, MG, i)), r) =
      let
        fun theoremToModeSpine' (I.Null, I.Null, mS) = mS
          | theoremToModeSpine' (I.Decl (G, I.Dec (x, _)), I.Decl (MG, m), mS) =
              theoremToModeSpine' (G, MG, M.Mapp (M.Marg (m, x), mS))
      in
        theoremToModeSpine' (G, MG, M.Mnil)
      end

  in
    let theoremDecToConDec = theoremDecToConDec
    let theoremDecToModeSpine = theoremDecToModeSpine
  end (* local *)

end;; (* functor ThmSyn *)
