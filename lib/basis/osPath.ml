(** OS.Path module - SML Basis Library OS_PATH signature *)

module type OS_PATH = sig
  exception Path
  exception InvalidArc

  type path_from_string = {isAbs : bool; vol : string; arcs : string list}

  val parentArc : string
  val currentArc : string

  val fromString : string -> path_from_string
  val toString : path_from_string -> string

  type dir_file = {dir : string; file : string}

  val getVolume : string -> string
  val getParent : string -> string

  val splitDirFile : string -> dir_file
  val joinDirFile : dir_file -> string
  val dir : string -> string
  val file : string -> string

  type base_ext = {base : string; ext : string option}

  val splitBaseExt : string -> base_ext
  val joinBaseExt : base_ext -> string
  val base : string -> string
  val ext : string -> string option

  type path_relative = {path : string; relativeTo : string}

  val mkCanonical : string -> string
  val isCanonical : string -> bool
  val mkAbsolute : path_relative -> string
  val mkRelative : path_relative -> string
  val isAbsolute : string -> bool
  val isRelative : string -> bool

  val concat : string -> string -> string
end

module OSPath : OS_PATH = struct
  exception Path
  exception InvalidArc

  type path_from_string = {isAbs : bool; vol : string; arcs : string list}
  type dir_file = {dir : string; file : string}
  type base_ext = {base : string; ext : string option}
  type path_relative = {path : string; relativeTo : string}

  let parentArc = ".."
  let currentArc = "."

  let is_separator c = c = '/' || c = '\\'

  let fromString path =
    (* Simplified Unix-style path parsing *)
    let isAbs = Stdlib.String.length path > 0 && Stdlib.String.get path 0 = '/' in
    let arcs = Stdlib.String.split_on_char '/' path |>
               Stdlib.List.filter (fun s -> s <> "") in
    {isAbs; vol = ""; arcs}

  let toString {isAbs; vol; arcs} =
    let prefix = if isAbs then "/" else "" in
    prefix ^ Stdlib.String.concat "/" arcs

  let getVolume _ = ""  (* No volume on Unix *)

  let getParent path =
    match Filename.dirname path with
    | "." -> ""
    | p -> p

  let splitDirFile path =
    {dir = Filename.dirname path; file = Filename.basename path}

  let joinDirFile {dir; file} =
    if dir = "" || dir = "." then file
    else Filename.concat dir file

  let dir = Filename.dirname
  let file = Filename.basename

  let splitBaseExt path =
    let base_name = Filename.basename path in
    try
      let dot_idx = Stdlib.String.rindex base_name '.' in
      if dot_idx = 0 then
        {base = base_name; ext = None}
      else
        let base = Stdlib.String.sub base_name 0 dot_idx in
        let ext = Stdlib.String.sub base_name (dot_idx + 1)
                    (Stdlib.String.length base_name - dot_idx - 1) in
        {base; ext = Some ext}
    with Not_found ->
      {base = base_name; ext = None}

  let joinBaseExt {base; ext} =
    match ext with
    | None -> base
    | Some e -> base ^ "." ^ e

  let base path =
    let {base; _} = splitBaseExt path in
    base

  let ext path =
    let {ext; _} = splitBaseExt path in
    ext

  let mkCanonical path = path  (* Placeholder *)
  let isCanonical _ = true     (* Placeholder *)

  let mkAbsolute {path; relativeTo} =
    if Filename.is_relative path then
      Filename.concat relativeTo path
    else
      path

  let mkRelative {path; relativeTo} = path  (* Placeholder *)

  let isAbsolute path = Filename.is_implicit path = false
  let isRelative path = Filename.is_relative path

  let concat p1 p2 = Filename.concat p1 p2
end
