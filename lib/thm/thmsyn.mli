(* Theorems *)
(* Author: Carsten Schuermann *)
(* Modified: Brigitte Pientka *)

(* GEN BEGIN SIGNATURE DECLARATION *) signature THMSYN =
sig
  structure Names : NAMES

  exception Error of string

  (*! type Param = string option !*)

  datatype order =
    Varg of string list
  | Lex of order list
  | Simul of order list

  (* -bp *)
  datatype predicate = Less | Leq | Eq

  datatype red_order = 
      RedOrder of predicate * order * order
  
  datatype callpats =
    Callpats of (IntSyn.cid * (string option) list) list 

  (* Termination declaration *)
  datatype t_decl = 
    TDecl of order * callpats

  (* -bp *)
  (* Reduction declaration *)
  datatype r_decl = 
    RDecl of (red_order * callpats)

   (* Tabled declaration *)
   datatype tabled_decl = 
    TabledDecl of IntSyn.cid

   (* KeepTable declaration *)
   datatype keep_table_decl = 
    KeepTableDecl of IntSyn.cid

  (* Theorem declaration  *)
  datatype th_decl =
    ThDecl of (IntSyn.dec IntSyn.ctx * IntSyn.dec IntSyn.ctx) list
              * IntSyn.dec IntSyn.ctx * ModeSyn.mode IntSyn.ctx * int

  (* Proof declaration *)
  datatype p_decl = 
    PDecl of int * t_decl

  (* World declaration *)
(*  datatype WDecl = 
    WDecl of (IntSyn.Dec IntSyn.Ctx * 
	      IntSyn.Dec IntSyn.Ctx) list * Callpats
*)
  datatype w_decl = 
    WDecl of Names.qid list * callpats

  val theoremDecToConDec : ((string * th_decl) * Paths.region) -> 
                           (IntSyn.dec IntSyn.ctx * IntSyn.dec IntSyn.ctx) list * IntSyn.con_dec
  val theoremDecToModeSpine : ((string * th_decl) * Paths.region) -> ModeSyn.mode_spine
end (* GEN END SIGNATURE DECLARATION *);  (* signature THMSYN *)
