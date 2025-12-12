(* Theorem Declarations *)
(* Author: Carsten Schuermann *)
(* Modified: Brigitte Pientka, Frank Pfenning *)

signature THM =
sig
  structure ThmSyn : THMSYN
  (*! structure Paths : PATHS !*)

  exception  Error of string

  val installTotal : ThmSyn.t_decl * (Paths.region * Paths.region list)
                     -> IntSyn.cid list
  val uninstallTotal : IntSyn.cid -> bool

  val installTerminates : ThmSyn.t_decl * (Paths.region * Paths.region list) 
                          -> IntSyn.cid list
  val uninstallTerminates : IntSyn.cid -> bool (* true: was declared, false not *)

  val installReduces : ThmSyn.r_decl * (Paths.region * Paths.region list) 
                       -> IntSyn.cid list 
  val uninstallReduces : IntSyn.cid -> bool

  val installTabled : ThmSyn.tabled_decl -> unit
  val installKeepTable : ThmSyn.keep_table_decl -> unit

end;  (* signature THM *)
