(** StringCvt module - SML Basis Library STRING_CVT signature *)

module type STRING_CVT = sig
  type radix = BIN | OCT | DEC | HEX

  type realfmt =
    | SCI of int option
    | FIX of int option
    | GEN of int option
    | EXACT

  type ('a, 'b) reader = 'b -> ('a * 'b) option

  val padLeft : char -> int -> string -> string
  val padRight : char -> int -> string -> string

  val splitl : (char -> bool)
               -> (char, 'a) reader
               -> 'a
               -> string * 'a

  val takel : (char -> bool)
              -> (char, 'a) reader
              -> 'a
              -> string

  val dropl : (char -> bool)
              -> (char, 'a) reader
              -> 'a
              -> 'a

  val skipWS : (char, 'a) reader -> 'a -> 'a

  type cs

  val scanString : ((char, cs) reader -> ('a, cs) reader)
                   -> string
                   -> 'a option
end

module StringCvt : STRING_CVT = struct
  (* Radix for integer conversions *)
  type radix = BIN | OCT | DEC | HEX

  (* Real number formatting *)
  type realfmt =
    | SCI of int option  (* Scientific notation with optional precision *)
    | FIX of int option  (* Fixed point with optional decimal places *)
    | GEN of int option  (* General format with optional significant digits *)
    | EXACT              (* Exact representation *)

  (* Reader type: converts a state to an optional (value, new_state) pair *)
  type ('a, 'b) reader = 'b -> ('a * 'b) option

  let padLeft c width s =
    let len = Stdlib.String.length s in
    if len >= width then s
    else Stdlib.String.make (width - len) c ^ s

  let padRight c width s =
    let len = Stdlib.String.length s in
    if len >= width then s
    else s ^ Stdlib.String.make (width - len) c

  let splitl pred reader state =
    let rec loop acc state =
      match reader state with
      | None -> (Stdlib.String.concat "" (Stdlib.List.rev acc), state)
      | Some (c, state') ->
          if pred c then
            loop (Stdlib.String.make 1 c :: acc) state'
          else
            (Stdlib.String.concat "" (Stdlib.List.rev acc), state)
    in
    loop [] state

  let takel pred reader state =
    let (s, _) = splitl pred reader state in
    s

  let dropl pred reader state =
    let (_, state') = splitl pred reader state in
    state'

  let isSpace c =
    c = ' ' || c = '\t' || c = '\n' || c = '\r' || c = '\011' || c = '\012'

  let skipWS reader state =
    dropl isSpace reader state

  (* Character stream type for scanString *)
  type cs = int  (* Position in string *)

  let scanString scanner str =
    (* Create a reader for strings *)
    let reader pos =
      if pos >= Stdlib.String.length str then None
      else Some (Stdlib.String.get str pos, pos + 1)
    in
    match scanner reader 0 with
    | None -> None
    | Some (result, _) -> Some result
end
