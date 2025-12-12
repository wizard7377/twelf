(* External Syntax for meta theorems *)
(* Author: Carsten Schuermann *)

(* GEN BEGIN SIGNATURE DECLARATION *) signature THMEXTSYN =
sig
  structure ExtSyn : EXTSYN
  (*! structure Paths : PATHS  !*)

  type order
  val varg : (Paths.region * string list) -> order
  val lex : (Paths.region * order list) -> order
  val simul : (Paths.region * order list) -> order

  type callpats
  val callpats : (string * string option list * Paths.region) list -> callpats

  type tdecl
  val tdecl : order * callpats -> tdecl

  (* -bp *)
  type predicate 
  val predicate : (string * Paths.region) -> predicate

  (* -bp *)
  type rdecl
  val rdecl : predicate * order * order * callpats -> rdecl

  type tableddecl
  val tableddecl :  (string * Paths.region) -> tableddecl

  type keep_tabledecl
  val keepTabledecl :  (string * Paths.region) -> keep_tabledecl

  type prove
  val prove : int * tdecl -> prove

  type establish
  val establish  : int * tdecl -> establish

  type assert
  val assert : callpats -> assert

  type decs
  type theorem
  type theoremdec

  val null : decs
  val decl : (decs * ExtSyn.dec) -> decs

  val top : theorem
  val exists : decs * theorem -> theorem
  val forall : decs * theorem -> theorem
  val forallStar : decs * theorem -> theorem
  val forallG : (decs * decs) list * theorem -> theorem

  val dec : (string * theorem) -> theoremdec

  (* world checker *)
  type wdecl
  val wdecl : (string list * string) list * callpats -> wdecl
(*  val wdecl : (decs * decs) list * callpats -> wdecl *)

end (* GEN END SIGNATURE DECLARATION *);  (* signature THMEXTSYN *)


(* GEN BEGIN SIGNATURE DECLARATION *) signature RECON_THM =
sig
  structure ThmSyn : THMSYN
  include THMEXTSYN

  exception Error of string
  val tdeclTotDecl : tdecl -> (ThmSyn.t_decl * (Paths.region * Paths.region list))
  val rdeclTorDecl : rdecl -> (ThmSyn.r_decl * (Paths.region * Paths.region list))

  val tableddeclTotabledDecl : tableddecl -> (ThmSyn.tabled_decl * Paths.region)
  val keepTabledeclToktDecl : keep_tabledecl -> (ThmSyn.keep_table_decl * Paths.region)


  val theoremToTheorem : theorem -> ThmSyn.th_decl
  val theoremDecToTheoremDec : theoremdec -> string * ThmSyn.th_decl
  val proveToProve : prove -> (ThmSyn.p_decl * (Paths.region * Paths.region list))
  val establishToEstablish : establish -> (ThmSyn.p_decl * (Paths.region * Paths.region list))
  val assertToAssert : assert -> (ThmSyn.callpats * Paths.region list)
  val wdeclTowDecl : wdecl -> (ThmSyn.w_decl * Paths.region list)
end (* GEN END SIGNATURE DECLARATION *);  (* signature RECON_THM *)
