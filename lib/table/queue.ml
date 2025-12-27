open Basis
open Common

(* Queues *)

(* Author: Frank Pfenning *)

module type QUEUE = sig
  type 'a queue

  val empty : 'a queue
  val insert : 'a * 'a queue -> 'a queue
  val delete : 'a queue -> ('a * 'a queue) option
  val insertFront : 'a * 'a queue -> 'a queue
  val deleteEnd : 'a queue -> ('a * 'a queue) option

  (* If  toList (q) ==> (l, SOME(q')) *)
  (* then q == q' and toList q' is constant time *)
  val toList : 'a queue -> 'a list * 'a queue option
end

(* signature QUEUE *)
(* Queues *)

(* Author: Frank Pfenning *)

(* Standard functional implementation of queues *)

(*
   Since in the typical use `delete' is not of constant amortized time we
   provide a special `toList' operation which permits constant
   amortized access under programmer control.
*)

module Queue : QUEUE = struct
  (* Representation invariant:
     If  q = (inp, out)  then  q == out @ rev(inp)
  *)

  type 'a queue = 'a list * 'a list

  let empty = ([], [])
  let rec insert (x, (inp, out)) = (x :: inp, out)

  let rec delete = function
    | [], [] -> None
    | inp, x :: out -> Some (x, (inp, out))
    | inp, [] -> delete ([], List.rev inp)

  let rec insertFront (x, (inp, out)) = (inp, x :: out)

  let rec deleteEnd = function
    | [], [] -> None
    | x :: inp, out -> Some (x, (inp, out))
    | [], out -> delete (List.rev out, [])
  (* toList q ==> (l, NONE)  means q == l and toList is constant time *)

  (* toList q ==> (l, SOME(q')) means q == l == q' *)

  (* and toList q' is constant time *)

  let rec toList = function
    | [], out -> (out, None)
    | inp, out ->
        let out' = out @ List.rev inp in
        (out', Some ([], out'))
end

(* structure Queue *)
