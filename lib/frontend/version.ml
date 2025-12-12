structure Version = 
struct

(* GEN BEGIN TAG INSIDE LET *) val current_version = "1.7.1" (* GEN END TAG INSIDE LET *)

(* GEN BEGIN TAG INSIDE LET *) val current_version_revision = "1813" (* GEN END TAG INSIDE LET *)

(* GEN BEGIN TAG INSIDE LET *) fun maybe true x = x
  | maybe false x = "" (* GEN END TAG INSIDE LET *)
  
(* GEN BEGIN TAG INSIDE LET *) val official = BuildId.revision = current_version_revision (* GEN END TAG INSIDE LET *)
(* GEN BEGIN TAG INSIDE LET *) val external = BuildId.revision = "exported" (* GEN END TAG INSIDE LET *)

(* GEN BEGIN TAG INSIDE LET *) val version_string = 
   "Twelf " ^ current_version ^ maybe (not official) "+" ^ " ("
   ^ maybe (not external andalso not official) ("r" ^ BuildId.revision ^ ", ")
   ^ "built " ^ BuildId.date ^ " on " ^ BuildId.hostname ^ ")" (* GEN END TAG INSIDE LET *)

end
