(* Stream Library *)


(* Author: Frank Pfenning *)


(* BASIC_STREAM defines the visible "core" of streams *)


module type BASIC_STREAM = sig
  type 'a stream
  type 'a front = Empty | Cons of 'a * 'a stream
(* Lazy stream construction and exposure *)
  val delay : (unit -> 'a front) -> 'a stream
  val expose : 'a stream -> 'a front
(* Eager stream construction *)
  val empty : 'a stream
  val cons : 'a * 'a stream -> 'a stream

end


module BasicStream : BASIC_STREAM = struct type 'a stream = Stream of unit -> 'a front and 'a front = Empty | Cons of 'a * 'a stream
let rec delay (d)  = Stream (d)
let rec expose (Stream (d))  = d ()
let empty = Stream (fun () -> Empty)
let rec cons (x, s)  = Stream (fun () -> Cons (x, s))
 end


(* Note that this implementation is NOT semantically *)


(* equivalent to the plain (non-memoizing) streams, since *)


(* effects will be executed only once in this implementation *)


module BasicMemoStream : BASIC_STREAM = struct type 'a stream = Stream of unit -> 'a front and 'a front = Empty | Cons of 'a * 'a stream
exception Uninitialized
let rec expose (Stream (d))  = d ()
let rec delay (d)  = ( let memo = ref (fun () -> raise (Uninitialized)) in let rec memoFun ()  = try ( let r = d () in  (memo := (fun () -> r); r) ) with exn -> (memo := (fun () -> raise (exn)); raise (exn)) in  memo := memoFun; Stream (fun () -> ! memo ()) )
let empty = Stream (fun () -> Empty)
let rec cons (x, s)  = Stream (fun () -> Cons (x, s))
 end


(* STREAM extends BASIC_STREAMS by operations *)


(* definable without reference to the implementation *)


module type STREAM = sig
  include BASIC_STREAM
  exception EmptyStream
  val null : 'a stream -> bool
  val hd : 'a stream -> 'a
  val tl : 'a stream -> 'a stream
  val map : ('a -> 'b) -> 'a stream -> 'b stream
  val filter : ('a -> bool) -> 'a stream -> 'a stream
  val exists : ('a -> bool) -> 'a stream -> bool
  val take : 'a stream * int -> 'a list
  val drop : 'a stream * int -> 'a stream
  val fromList : 'a list -> 'a stream
  val toList : 'a stream -> 'a list
  val tabulate : (int -> 'a) -> 'a stream

end


module Stream (BasicStream : BASIC_STREAM) : STREAM = struct open BasicStream
exception EmptyStream
(* functions null, hd, tl, map, filter, exists, take, drop *)

(* parallel the functions in the List structure *)

let rec null (s)  = null' (expose s)
and null' = function (Empty) -> true | (Cons _) -> false
let rec hd (s)  = hd' (expose s)
and hd' = function (Empty) -> raise (EmptyStream) | (Cons (x, s)) -> x
let rec tl (s)  = tl' (expose s)
and tl' = function (Empty) -> raise (EmptyStream) | (Cons (x, s)) -> s
let rec map f s  = delay (fun () -> map' f (expose s))
and map' = function (f, (Empty)) -> Empty | (f, (Cons (x, s))) -> Cons (f (x), map f s)
let rec filter p s  = delay (fun () -> filter' p (expose s))
and filter' = function (p, (Empty)) -> Empty | (p, (Cons (x, s))) -> if p (x) then Cons (x, filter p s) else filter' p (expose s)
let rec exists p s  = exists' p (expose s)
and exists' = function (p, (Empty)) -> false | (p, (Cons (x, s))) -> p (x) || exists p s
let rec takePos = function (s, 0) -> [] | (s, n) -> take' (expose s, n)
and take' = function (Empty, _) -> [] | (Cons (x, s), n) -> x :: takePos (s, n - 1)
let rec take (s, n)  = if n < 0 then raise (Subscript) else takePos (s, n)
let rec fromList = function ([]) -> empty | (x :: l) -> cons (x, fromList (l))
let rec toList (s)  = toList' (expose s)
and toList' = function (Empty) -> [] | (Cons (x, s)) -> x :: toList (s)
let rec dropPos = function (s, 0) -> s | (s, n) -> drop' (expose s, n)
and drop' = function (Empty, _) -> empty | (Cons (x, s), n) -> dropPos (s, n - 1)
let rec drop (s, n)  = if n < 0 then raise (Subscript) else dropPos (s, n)
let rec tabulate f  = delay (fun () -> tabulate' f)
and tabulate' f  = Cons (f (0), tabulate (fun i -> f (i + 1)))
 end


(* structure Stream :> STREAM --- non-memoizing *)


module Stream : STREAM = Stream (struct module BasicStream = BasicStream end)


(* structure MStream :> STREAM --- memoizing *)


module MStream : STREAM = Stream (struct module BasicStream = BasicMemoStream end)


(*
structure S = Stream;  (* abbreviation *)

(* simple definition *)
fun ones' () = S.Cons(1, S.delay ones');
val ones = S.delay ones';

(* alternative definitions *)
val ones = S.tabulate (fn _ => 1);
val nats = S.tabulate (fn i => i);
val poss = S.map (fn i => i+1) nats;
val evens = S.map (fn i => 2*i) nats;

(* notMultiple p q >=> true iff q is not a multiple of p *)
fun notMultiple p q = (q mod p <> 0);

fun sieve s = S.delay (fn () => sieve' (S.expose s))
and sieve' (S.Empty) = S.Empty
  | sieve' (S.Cons(p, s)) =
      S.Cons (p, sieve (S.filter (notMultiple p) s));

val primes = sieve (S.tabulate (fn i => i+2));
*)

