(** ListPair module - SML Basis Library LIST_PAIR signature *)

open Order

module type LIST_PAIR = sig
  exception UnequalLengths

  val zip : 'a list * 'b list -> ('a * 'b) list
  val zipEq : 'a list * 'b list -> ('a * 'b) list
  val unzip : ('a * 'b) list -> 'a list * 'b list
  val app : ('a * 'b -> unit) -> 'a list * 'b list -> unit
  val appEq : ('a * 'b -> unit) -> 'a list * 'b list -> unit
  val map : ('a * 'b -> 'c) -> 'a list * 'b list -> 'c list
  val mapEq : ('a * 'b -> 'c) -> 'a list * 'b list -> 'c list
  val foldl : ('a * 'b * 'c -> 'c) -> 'c -> 'a list * 'b list -> 'c
  val foldlEq : ('a * 'b * 'c -> 'c) -> 'c -> 'a list * 'b list -> 'c
  val foldr : ('a * 'b * 'c -> 'c) -> 'c -> 'a list * 'b list -> 'c
  val foldrEq : ('a * 'b * 'c -> 'c) -> 'c -> 'a list * 'b list -> 'c
  val all : ('a * 'b -> bool) -> 'a list * 'b list -> bool
  val exists : ('a * 'b -> bool) -> 'a list * 'b list -> bool
  val allEq : ('a * 'b -> bool) -> 'a list * 'b list -> bool
end

module ListPair : LIST_PAIR = struct
  exception UnequalLengths

  let rec zip (l1, l2) =
    match (l1, l2) with
    | ([], []) -> []
    | ([], _) -> []
    | (_, []) -> []
    | (x::xs, y::ys) -> (x, y) :: zip (xs, ys)

  let rec zipEq (l1, l2) =
    match (l1, l2) with
    | ([], []) -> []
    | (x::xs, y::ys) -> (x, y) :: zipEq (xs, ys)
    | _ -> raise UnequalLengths

  let rec unzip pairs =
    match pairs with
    | [] -> ([], [])
    | (x, y) :: rest ->
        let (xs, ys) = unzip rest in
        (x :: xs, y :: ys)

  let rec app f (l1, l2) =
    match (l1, l2) with
    | ([], _) -> ()
    | (_, []) -> ()
    | (x::xs, y::ys) ->
        f (x, y);
        app f (xs, ys)

  let rec appEq f (l1, l2) =
    match (l1, l2) with
    | ([], []) -> ()
    | (x::xs, y::ys) ->
        f (x, y);
        appEq f (xs, ys)
    | _ -> raise UnequalLengths

  let rec map f (l1, l2) =
    match (l1, l2) with
    | ([], _) -> []
    | (_, []) -> []
    | (x::xs, y::ys) -> f (x, y) :: map f (xs, ys)

  let rec mapEq f (l1, l2) =
    match (l1, l2) with
    | ([], []) -> []
    | (x::xs, y::ys) -> f (x, y) :: mapEq f (xs, ys)
    | _ -> raise UnequalLengths

  let rec foldl f init (l1, l2) =
    match (l1, l2) with
    | ([], _) -> init
    | (_, []) -> init
    | (x::xs, y::ys) -> foldl f (f (x, y, init)) (xs, ys)

  let rec foldlEq f init (l1, l2) =
    match (l1, l2) with
    | ([], []) -> init
    | (x::xs, y::ys) -> foldlEq f (f (x, y, init)) (xs, ys)
    | _ -> raise UnequalLengths

  let rec foldr f init (l1, l2) =
    match (l1, l2) with
    | ([], _) -> init
    | (_, []) -> init
    | (x::xs, y::ys) -> f (x, y, foldr f init (xs, ys))

  let rec foldrEq f init (l1, l2) =
    match (l1, l2) with
    | ([], []) -> init
    | (x::xs, y::ys) -> f (x, y, foldrEq f init (xs, ys))
    | _ -> raise UnequalLengths

  let rec all pred (l1, l2) =
    match (l1, l2) with
    | ([], _) -> true
    | (_, []) -> true
    | (x::xs, y::ys) -> pred (x, y) && all pred (xs, ys)

  let rec exists pred (l1, l2) =
    match (l1, l2) with
    | ([], _) -> false
    | (_, []) -> false
    | (x::xs, y::ys) -> pred (x, y) || exists pred (xs, ys)

  let rec allEq pred (l1, l2) =
    match (l1, l2) with
    | ([], []) -> true
    | (x::xs, y::ys) -> pred (x, y) && allEq pred (xs, ys)
    | _ -> raise UnequalLengths
end
