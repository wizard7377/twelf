(* Theorems *)
(* Author: Carsten Schuermann *)
(* Modified: Brigitte Pientka *)

module type THMSYN =
sig
  module Names : NAMES

  exception Error of string

  (*! type Param = string option !*)

  type order =
    Varg of string list
  | Lex of order list
  | Simul of order list

  (* -bp *)
  type predicate = Less | Leq | Eq

  type redOrder = 
      RedOrder of predicate * order * order
  
  type callpats =
    Callpats of (IntSyn.cid * (string option) list) list 

  (* Termination declaration *)
  type tDecl = 
    TDecl of order * callpats

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

  (* Theorem declaration  *)
  type thDecl =
    ThDecl of (IntSyn.Dec IntSyn.ctx * IntSyn.Dec IntSyn.ctx) list
              * IntSyn.Dec IntSyn.ctx * ModeSyn.Mode IntSyn.ctx * int

  (* Proof declaration *)
  type pDecl = 
    PDecl of int * tDecl

  (* World declaration *)
(*  type WDecl = 
    WDecl of (IntSyn.Dec IntSyn.ctx * 
	      IntSyn.Dec IntSyn.ctx) list * Callpats
*)
  type wDecl = 
    WDecl of Names.Qid list * callpats

  val theoremDecToConDec : ((string * thDecl) * Paths.region) -> 
                           (IntSyn.Dec IntSyn.ctx * IntSyn.Dec IntSyn.ctx) list * IntSyn.ConDec
  val theoremDecToModeSpine : ((string * thDecl) * Paths.region) -> ModeSyn.modeSpine
end;; (* module type THMSYN *)
