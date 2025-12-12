(* Parsing Theorems *)
(* Author: Carsten Schuermann *)

(* GEN BEGIN SIGNATURE DECLARATION *) signature PARSE_THM =
sig

  (*! structure Parsing : PARSING !*)
  structure ThmExtSyn: THMEXTSYN

  val parseTotal' : ThmExtSyn.tdecl Parsing.parser (* -fp *)
  val parseTerminates' : ThmExtSyn.tdecl Parsing.parser
  val parseReduces' : ThmExtSyn.rdecl Parsing.parser      (* -bp *)
  val parseTabled' : ThmExtSyn.tableddecl Parsing.parser  (* -bp *)
  val parseKeepTable' : ThmExtSyn.keep_tabledecl Parsing.parser  (* -bp *)
  val parseTheorem' : ThmExtSyn.theorem Parsing.parser
  val parseTheoremDec' : ThmExtSyn.theoremdec Parsing.parser
  val parseWorlds' : ThmExtSyn.wdecl Parsing.parser
  val parseProve' : ThmExtSyn.prove Parsing.parser
  val parseEstablish' : ThmExtSyn.establish Parsing.parser
  val parseAssert' : ThmExtSyn.assert Parsing.parser

end (* GEN END SIGNATURE DECLARATION *);  (* signature PARSE_THM *)
