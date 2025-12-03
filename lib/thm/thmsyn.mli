(* Theorems *)
(* Author: Carsten Schuermann *)
(* Modified: Brigitte Pientka *)

module type THMSYN =
sig
  module Names : NAMES

  exception Error of string

  (*! type Param = string option !*)

  type Order =
    Varg of string list
  | Lex of Order list
  | Simul of Order list

  (* -bp *)
  type Predicate = Less | Leq | Eq

  type RedOrder = 
      RedOrder of Predicate * Order * Order
  
  type Callpats =
    Callpats of (IntSyn.cid * (string option) list) list 

  (* Termination declaration *)
  type TDecl = 
    TDecl of Order * Callpats

  (* -bp *)
  (* Reduction declaration *)
  type RDecl = 
    RDecl of (RedOrder * Callpats)

   (* Tabled declaration *)
   type TabledDecl = 
    TabledDecl of IntSyn.cid

   (* KeepTable declaration *)
   type KeepTableDecl = 
    KeepTableDecl of IntSyn.cid

  (* Theorem declaration  *)
  type ThDecl =
    ThDecl of (IntSyn.Dec IntSyn.Ctx * IntSyn.Dec IntSyn.Ctx) list
              * IntSyn.Dec IntSyn.Ctx * ModeSyn.Mode IntSyn.Ctx * int

  (* Proof declaration *)
  type PDecl = 
    PDecl of int * TDecl

  (* World declaration *)
(*  type WDecl = 
    WDecl of (IntSyn.Dec IntSyn.Ctx * 
	      IntSyn.Dec IntSyn.Ctx) list * Callpats
*)
  type WDecl = 
    WDecl of Names.Qid list * Callpats

  val theoremDecToConDec : ((string * ThDecl) * Paths.region) -> 
                           (IntSyn.Dec IntSyn.Ctx * IntSyn.Dec IntSyn.Ctx) list * IntSyn.ConDec
  val theoremDecToModeSpine : ((string * ThDecl) * Paths.region) -> ModeSyn.ModeSpine
end;  (* module type THMSYN *)
