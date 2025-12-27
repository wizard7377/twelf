(** Substring module - SML Basis Library SUBSTRING signature *)

open Order
open List
module type SUBSTRING = sig
  type substring

  val sub : string * int * int -> substring
  val full : string -> substring
  val string : substring -> string
  val extract : string * int * int option -> substring
  val slice : substring * int * int option -> substring

  val base : substring -> string * int * int
  val isEmpty : substring -> bool
  val getc : substring -> (char * substring) option
  val first : substring -> char option
  val triml : int -> substring -> substring
  val trimr : int -> substring -> substring
  val size : substring -> int

  val explode : substring -> char list
  val isPrefix : string -> substring -> bool
  val isSubstring : string -> substring -> bool
  val isSuffix : string -> substring -> bool

  val compare : substring * substring -> order
  val collate : (char * char -> order)
                -> substring * substring -> order

  val splitl : (char -> bool)
               -> substring
               -> substring * substring

  val splitr : (char -> bool)
               -> substring
               -> substring * substring

  val splitAt : substring * int -> substring * substring
  val dropl : (char -> bool) -> substring -> substring
  val dropr : (char -> bool) -> substring -> substring
  val takel : (char -> bool) -> substring -> substring
  val taker : (char -> bool) -> substring -> substring

  val position : string -> substring -> substring * substring

  val span : substring * substring -> substring
  val translate : (char -> string) -> substring -> string

  val tokens : (char -> bool) -> substring -> substring list
  val fields : (char -> bool) -> substring -> substring list

  val app : (char -> unit) -> substring -> unit
  val foldl : (char * 'a -> 'a) -> 'a -> substring -> 'a
  val foldr : (char * 'a -> 'a) -> 'a -> substring -> 'a
end

module Substring : SUBSTRING = struct
  (* A substring is represented as (string, start, length) *)
  type substring = string * int * int

  let sub (s, start, len) =
    if start < 0 || len < 0 || start + len > Stdlib.String.length s then
      raise (Invalid_argument "Substring.sub")
    else
      (s, start, len)

  let full s = (s, 0, Stdlib.String.length s)

  let string (s, start, len) =
    Stdlib.String.sub s start len

  let extract (s, start, len_opt) =
    let slen = Stdlib.String.length s in
    if start < 0 || start > slen then
      raise (Invalid_argument "Substring.extract")
    else
      match len_opt with
      | None -> (s, start, slen - start)
      | Some len ->
          if len < 0 || start + len > slen then
            raise (Invalid_argument "Substring.extract")
          else
            (s, start, len)

  let slice ((s, start, len), i, len_opt) =
    if i < 0 || i > len then
      raise (Invalid_argument "Substring.slice")
    else
      match len_opt with
      | None -> (s, start + i, len - i)
      | Some n ->
          if n < 0 || i + n > len then
            raise (Invalid_argument "Substring.slice")
          else
            (s, start + i, n)

  let base ss = ss

  let isEmpty (_, _, len) = len = 0

  let getc (s, start, len) =
    if len = 0 then None
    else Some (Stdlib.String.get s start, (s, start + 1, len - 1))

  let first (s, start, len) =
    if len = 0 then None
    else Some (Stdlib.String.get s start)

  let triml k (s, start, len) =
    if k < 0 then raise (Invalid_argument "Substring.triml")
    else if k >= len then (s, start + len, 0)
    else (s, start + k, len - k)

  let trimr k (s, start, len) =
    if k < 0 then raise (Invalid_argument "Substring.trimr")
    else if k >= len then (s, start, 0)
    else (s, start, len - k)

  let size (_, _, len) = len

  let explode (s, start, len) =
    let rec loop i acc =
      if i < 0 then acc
      else loop (i - 1) (Stdlib.String.get s (start + i) :: acc)
    in
    loop (len - 1) []

  let isPrefix prefix (s, start, len) =
    let plen = Stdlib.String.length prefix in
    if plen > len then false
    else
      let rec loop i =
        if i >= plen then true
        else if Stdlib.String.get prefix i <> Stdlib.String.get s (start + i) then false
        else loop (i + 1)
      in
      loop 0

  let isSubstring needle (s, start, len) =
    let nlen = Stdlib.String.length needle in
    if nlen = 0 then true
    else if nlen > len then false
    else
      let rec check_at pos =
        if pos + nlen > start + len then false
        else
          let rec match_from i =
            if i >= nlen then true
            else if Stdlib.String.get needle i <> Stdlib.String.get s (pos + i) then false
            else match_from (i + 1)
          in
          if match_from 0 then true
          else check_at (pos + 1)
      in
      check_at start

  let isSuffix suffix (s, start, len) =
    let slen = Stdlib.String.length suffix in
    if slen > len then false
    else
      let offset = start + len - slen in
      let rec loop i =
        if i >= slen then true
        else if Stdlib.String.get suffix i <> Stdlib.String.get s (offset + i) then false
        else loop (i + 1)
      in
      loop 0

  let compare ((s1, start1, len1), (s2, start2, len2)) =
    let minlen = min len1 len2 in
    let rec loop i =
      if i >= minlen then
        if len1 < len2 then Less
        else if len1 > len2 then Greater
        else Equal
      else
        let c1 = Stdlib.String.get s1 (start1 + i) in
        let c2 = Stdlib.String.get s2 (start2 + i) in
        if c1 < c2 then Less
        else if c1 > c2 then Greater
        else loop (i + 1)
    in
    loop 0

  let collate cmp ((s1, start1, len1), (s2, start2, len2)) =
    let minlen = min len1 len2 in
    let rec loop i =
      if i >= minlen then
        if len1 < len2 then Less
        else if len1 > len2 then Greater
        else Equal
      else
        let c1 = Stdlib.String.get s1 (start1 + i) in
        let c2 = Stdlib.String.get s2 (start2 + i) in
        match cmp (c1, c2) with
        | Equal -> loop (i + 1)
        | ord -> ord
    in
    loop 0

  let splitl pred (s, start, len) =
    let rec loop i =
      if i >= len then i
      else if pred (Stdlib.String.get s (start + i)) then loop (i + 1)
      else i
    in
    let n = loop 0 in
    ((s, start, n), (s, start + n, len - n))

  let splitr pred (s, start, len) =
    let rec loop i =
      if i < 0 then -1
      else if pred (Stdlib.String.get s (start + i)) then loop (i - 1)
      else i
    in
    let n = loop (len - 1) in
    ((s, start, n + 1), (s, start + n + 1, len - n - 1))

  let splitAt ((s, start, len), i) =
    if i < 0 || i > len then
      raise (Invalid_argument "Substring.splitAt")
    else
      ((s, start, i), (s, start + i, len - i))

  let dropl pred ss =
    let (_, right) = splitl pred ss in
    right

  let dropr pred ss =
    let (left, _) = splitr pred ss in
    left

  let takel pred ss =
    let (left, _) = splitl pred ss in
    left

  let taker pred ss =
    let (_, right) = splitr pred ss in
    right

  let position needle (s, start, len) =
    let nlen = Stdlib.String.length needle in
    if nlen = 0 then ((s, start, 0), (s, start, len))
    else if nlen > len then ((s, start, len), (s, start + len, 0))
    else
      let rec check_at pos =
        if pos + nlen > start + len then None
        else
          let rec match_from i =
            if i >= nlen then true
            else if Stdlib.String.get needle i <> Stdlib.String.get s (pos + i) then false
            else match_from (i + 1)
          in
          if match_from 0 then Some pos
          else check_at (pos + 1)
      in
      match check_at start with
      | None -> ((s, start, len), (s, start + len, 0))
      | Some pos ->
          let prefix_len = pos - start in
          ((s, start, prefix_len), (s, pos, len - prefix_len))

  let span ((s1, start1, len1), (s2, start2, len2)) =
    (* Spans must be from the same base string *)
    if s1 != s2 then raise (Invalid_argument "Substring.span")
    else
      let start = min start1 start2 in
      let end_ = max (start1 + len1) (start2 + len2) in
      (s1, start, end_ - start)

  let translate f (s, start, len) =
    let buf = Buffer.create len in
    for i = 0 to len - 1 do
      Buffer.add_string buf (f (Stdlib.String.get s (start + i)))
    done;
    Buffer.contents buf

  let tokens pred ss =
    let rec loop acc ss =
      if isEmpty ss then List.rev acc
      else
        let ss' = dropl pred ss in
        if isEmpty ss' then List.rev acc
        else
          let (tok, rest) = splitl (fun c -> not (pred c)) ss' in
          loop (tok :: acc) rest
    in
    loop [] ss

  let fields pred ss =
    let rec loop acc ss =
      let (field, rest) = splitl (fun c -> not (pred c)) ss in
      if isEmpty rest then List.rev (field :: acc)
      else loop (field :: acc) (triml 1 rest)
    in
    loop [] ss

  let app f (s, start, len) =
    for i = 0 to len - 1 do
      f (Stdlib.String.get s (start + i))
    done

  let foldl f init (s, start, len) =
    let rec loop i acc =
      if i >= len then acc
      else loop (i + 1) (f (Stdlib.String.get s (start + i), acc))
    in
    loop 0 init

  let foldr f init (s, start, len) =
    let rec loop i acc =
      if i < 0 then acc
      else loop (i - 1) (f (Stdlib.String.get s (start + i), acc))
    in
    loop (len - 1) init
end
