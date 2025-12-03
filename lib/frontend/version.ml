module Version = 
struct

let current_version = "1.7.1"

let current_version_revision = "1813"

let rec maybe true x = x
  | maybe false x = ""
  
let official = BuildId.revision = current_version_revision
let external = BuildId.revision = "exported"

let version_string = 
   "Twelf " ^ current_version ^ maybe (not official) "+" ^ " ("
   ^ maybe (not external andalso not official) ("r" ^ BuildId.revision ^ ", ")
   ^ "built " ^ BuildId.date ^ " on " ^ BuildId.hostname ^ ")"

end
