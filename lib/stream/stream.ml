(* Stream Library *)
(* Author: Frank Pfenning *)

(* BASIC_STREAM defines the visible "core" of streams *)
module type BASIC_STREAM =
sig
  type 'a stream
  type 'a front = Empty | Cons of 'a * 'a stream

  (* Lazy stream construction and exposure *)
  let delay : (unit -> 'a front) -> 'a stream
  let expose : 'a stream -> 'a front

  (* Eager stream construction *)
  let empty : 'a stream
  let cons : 'a * 'a stream -> 'a stream
end;

(BasicStream : BASIC_STREAM) =
struct
  type 'a stream = Stream of unit -> 'a front
  and 'a front = Empty | Cons of 'a * 'a stream

  let rec delay (d) = Stream(d)
  let rec expose (Stream(d)) = d ()

  let empty = Stream (fn () => Empty)
  let rec cons (x, s) = Stream (fn () => Cons (x, s))
end;

(* Note that this implementation is NOT semantically *)
(* equivalent to the plain (non-memoizing) streams, since *)
(* effects will be executed only once in this implementation *)
(BasicMemoStream : BASIC_STREAM) =
struct

  type 'a stream = Stream of unit -> 'a front
  and 'a front = Empty | Cons of 'a * 'a stream

  exception Uninitialized

  let rec expose (Stream (d)) = d ()
  let rec delay (d) =
      let let memo = ref (fn () => raise Uninitialized)
	  let rec memoFun () =
	      let
		  let r = d ()
	       in
		  ( memo := (fn () => r) ; r )
	      end
	      handle exn => ( memo := (fn () => raise exn) ; raise exn )
      in
	memo := memoFun ; Stream (fn () => !memo ())
      end

  let empty = Stream (fn () => Empty)
  let rec cons (x, s) = Stream (fn () => Cons (x, s))
end;

(* STREAM extends BASIC_STREAMS by operations *)
(* definable without reference to the implementation *)
module type STREAM =
sig
  include BASIC_STREAM

  exception EmptyStream
  let null : 'a stream -> bool
  let hd : 'a stream -> 'a
  let tl : 'a stream -> 'a stream

  let map : ('a -> 'b) -> 'a stream -> 'b stream
  let filter : ('a -> bool) -> 'a stream -> 'a stream
  let exists : ('a -> bool) -> 'a stream -> bool

  let take : 'a stream * int -> 'a list
  let drop : 'a stream * int -> 'a stream

  let fromList : 'a list -> 'a stream
  let toList : 'a stream -> 'a list

  let tabulate : (int -> 'a) -> 'a stream
end;

module Stream
  (BasicStream : BASIC_STREAM) : STREAM =
struct
  open BasicStream

  exception EmptyStream

  (* functions null, hd, tl, map, filter, exists, take, drop *)
  (* parallel the functions in the List module *)
  let rec null (s) = null' (expose s)
  and null' (Empty) = true
    | null' (Cons _) = false

  let rec hd (s) = hd' (expose s)
  and hd' (Empty) = raise EmptyStream
    | hd' (Cons (x,s)) = x

  let rec tl (s) = tl' (expose s)
  and tl' (Empty) = raise EmptyStream
    | tl' (Cons (x,s)) = s

  let rec map f s = delay (fn () => map' f (expose s))
  and map' f (Empty) = Empty
    | map' f (Cons(x,s)) = Cons (f(x), map f s)

  let rec filter p s = delay (fn () => filter' p (expose s))
  and filter' p (Empty) = Empty
    | filter' p (Cons(x,s)) =
        if p(x) then Cons (x, filter p s)
	else filter' p (expose s)

  let rec exists p s = exists' p (expose s)
  and exists' p (Empty) = false
    | exists' p (Cons(x,s)) =
        p(x) orelse exists p s

  let rec takePos = function (s, 0) -> nil
    | (s, n) -> take' (expose s, n)
  and take' (Empty, _) = nil
    | take' (Cons(x,s), n) = x::takePos(s, n-1)

  let rec take (s,n) = if n < 0 then raise Subscript else takePos (s,n)

  let rec fromList = function (nil) -> empty
    | (x::l) -> cons(x,fromList(l))

  let rec toList (s) = toList' (expose s)
  and toList' (Empty) = nil
    | toList' (Cons(x,s)) = x::toList(s)

  let rec dropPos = function (s, 0) -> s
    | (s, n) -> drop' (expose s, n)
  and drop' (Empty, _) = empty
    | drop' (Cons(x,s), n) = dropPos (s, n-1)

  let rec drop (s,n) = if n < 0 then raise Subscript else dropPos (s,n)

  let rec tabulate f = delay (fn () => tabulate' f)
  and tabulate' f = Cons (f(0), tabulate (fun i -> f(i+1)))

end;

(* (Stream : STREAM) --- non-memoizing *)
(Stream : STREAM) =
  Stream (module BasicStream = BasicStream);

(* (MStream : STREAM) --- memoizing *)
(MStream : STREAM) =
  Stream (module BasicStream = BasicMemoStream);

(*
module S = Stream;  (* abbreviation *)

(* simple definition *)
let rec ones' () = S.Cons(1, S.delay ones');
let ones = S.delay ones';

(* alternative definitions *)
let ones = S.tabulate (fun _ -> 1);
let nats = S.tabulate (fun i -> i);
let poss = S.map (fun i -> i+1) nats;
let evens = S.map (fun i -> 2*i) nats;

(* notMultiple p q >=> true iff q is not a multiple of p *)
let rec notMultiple p q = (q mod p <> 0);

let rec sieve s = S.delay (fn () => sieve' (S.expose s))
and sieve' (S.Empty) = S.Empty
  | sieve' (S.Cons(p, s)) =
      S.Cons (p, sieve (S.filter (notMultiple p) s));

let primes = sieve (S.tabulate (fun i -> i+2));
*)
