open Basis ;; 

module Version = struct
  let current_version = "1.7.1"
  let current_version_revision = "1813"
  let rec maybe = function true, x -> x | false, x -> ""
  let official = BuildId.revision = current_version_revision
  let external_ = BuildId.revision = "exported"

  let version_string =
    "Twelf " ^ current_version ^ maybe (not official) "+" ^ " ("
    ^ maybe ((not external_) && not official) ("r" ^ BuildId.revision ^ ", ")
    ^ "built " ^ BuildId.date ^ " on " ^ BuildId.hostname ^ ")"
end
