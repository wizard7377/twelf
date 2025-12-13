structure Version = 
struct

(* GEN BEGIN TAG OUTSIDE LET *) val current_version = "1.7.1" (* GEN END TAG OUTSIDE LET *)

(* GEN BEGIN TAG OUTSIDE LET *) val current_version_revision = "1813" (* GEN END TAG OUTSIDE LET *)

fun (* GEN BEGIN CASE FIRST *) (* GEN BEGIN CASE FIRST *) maybe true x = x (* GEN END CASE FIRST *) (* GEN END CASE FIRST *)
  | (* GEN BEGIN CASE BRANCH *) (* GEN BEGIN CASE BRANCH *) maybe false x = "" (* GEN END CASE BRANCH *) (* GEN END CASE BRANCH *)
  
(* GEN BEGIN TAG OUTSIDE LET *) val official = BuildId.revision = current_version_revision (* GEN END TAG OUTSIDE LET *)
(* GEN BEGIN TAG OUTSIDE LET *) val external = BuildId.revision = "exported" (* GEN END TAG OUTSIDE LET *)

(* GEN BEGIN TAG OUTSIDE LET *) val version_string = 
   "Twelf " ^ current_version ^ maybe (not official) "+" ^ " ("
   ^ maybe (not external andalso not official) ("r" ^ BuildId.revision ^ ", ")
   ^ "built " ^ BuildId.date ^ " on " ^ BuildId.hostname ^ ")" (* GEN END TAG OUTSIDE LET *)

end
