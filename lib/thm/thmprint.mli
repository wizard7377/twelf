(* Printer for Meta Theorems *)
(* Author: Carsten Schuermann *)

(* GEN BEGIN SIGNATURE DECLARATION *) signature THMPRINT =
sig
  structure ThmSyn : THMSYN

  val tDeclToString : ThmSyn.t_decl -> string
  val callpatsToString : ThmSyn.callpats -> string
  val rDeclToString : ThmSyn.r_decl -> string                    (* -bp *)
  val ROrderToString: ThmSyn.red_order -> string                 (* -bp *)
  val tabledDeclToString: ThmSyn.tabled_decl -> string           (* -bp *)
  val keepTableDeclToString: ThmSyn.keep_table_decl -> string        (* -bp *)

end (* GEN END SIGNATURE DECLARATION *);  (* signature THMPRINT *)
