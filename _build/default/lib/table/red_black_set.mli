(* Sets *)
(* Author: Brigitte Pientka *)

(* This provides a common interface to ordered sets *)
(* based on red/black trees *)

(* GEN BEGIN SIGNATURE DECLARATION *) signature RBSET =

sig
  type key = int (* parameter *)
  type 'a entry = key * 'a

  exception Error of string

  type 'a ord_set
  val new : unit -> 'a ord_set		
  val copy : 'a ord_set -> 'a ord_set		

  val insert : 'a ord_set -> 'a entry -> unit
  val insertList : 'a ord_set -> ('a entry) list -> unit
  val insertShadow : 'a ord_set -> 'a entry -> unit

  val insertLast : 'a ord_set -> 'a -> unit

(*  val delete : 'a ordSet -> key -> unit*)

  val lookup : 'a ord_set -> key -> 'a option  

  val isEmpty : 'a ord_set -> bool
  val last : 'a ord_set -> 'a entry

  val clear : 'a ord_set -> unit

  (* Applies f:'a -> unit to all entries in the set
     pre-order traversal *)
  val app : 'a ord_set -> ('a -> unit) -> unit
  val update : 'a ord_set -> ('a -> 'a) -> 'a ord_set

  (* Applies f:'a entry -> unit to all entries in the set
     pre-order traversal *)
  val forall : 'a ord_set -> ('a entry -> unit) -> unit
(*  val exists : 'a ordSet -> ('a entry -> 'b option) -> ('a entry (* key * 'a *) * 'b) option *)
  val exists : 'a ord_set -> ('a entry -> bool) -> bool
  val existsOpt : 'a ord_set -> ('a -> bool) -> int option

  val size : 'a ord_set -> int
  val union: 'a ord_set -> 'a ord_set -> 'a ord_set
  val difference: 'a ord_set -> 'a ord_set -> 'a ord_set
  val difference2: 'a ord_set -> 'a ord_set -> ('a ord_set * 'a ord_set)
  val differenceModulo: 'a ord_set -> 'b ord_set -> ('a -> 'b -> unit) -> ('a ord_set * 'b ord_set)
  (* splits two sets into S1, S2, S3 *)
  val splitSets: 'a ord_set -> 'a ord_set -> ('a -> 'a -> 'a option) -> ('a ord_set * 'a ord_set * 'a ord_set)
  val intersection: 'a ord_set -> 'a ord_set -> 'a ord_set

end (* GEN END SIGNATURE DECLARATION *);  (* signature RBSET *)
