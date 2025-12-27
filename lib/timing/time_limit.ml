(* time-limit.sml
 *
 * COPYRIGHT (c) 1993 by AT&T Bell Laboratories.  See COPYRIGHT file for_sml details.
 * Modified: Brigitte Pientka
 *)
open Basis
open Common

module TimeLimit : sig
  exception TimeOut

  val timeLimit : Time.t option -> ('a -> 'b) -> 'a -> 'b
end = struct
  exception TimeOut

  let rec timeLimit = function
    | None -> fun f x -> f x
    | Some t ->
        fun f x ->
          print ("TIME LIMIT : " ^ Time.toString t ^ "sec \n");
          todo_hole
end

(* TimeLimit *)
