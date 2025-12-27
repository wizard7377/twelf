open Basis

(* Integers Modulo a Prime Number *)

(* Author: Roberto Virga *)

module IntegersMod (P : sig
  val p : int
end) : Field.FIELD = struct
  let p = P.p
  let name = "integer" ^ Integer.toString p

  type number = int

  let rec normalize n = n mod p
  let zero = 0
  let one = 1

  exception Div

  let ( ~- ) n = p - n
  let ( + ) (m, n) = normalize (m + n)
  let ( - ) (m, n) = normalize (m - n)
  let ( * ) (m, n) = normalize (m * n)

  let rec inverse = function
    | 0 -> raise Div
    | n ->
        (* alternative: compute n^(p-2) *)
        let rec inverse' i =
          if normalize (( * ) (n, i)) = 1 then i
          else inverse' (Stdlib.( + ) i 1)
        in
        inverse' 1

  let rec fromInt n = normalize n

  let rec fromString str =
    let check = List.all Char.isDigit in
    if check (String.explode str) then
      match Integer.fromString str with
      | Some n -> if n < p then Some n else None
      | None -> None
    else None

  let toString = Integer.toString
end

(* functor IntegersMod *)
