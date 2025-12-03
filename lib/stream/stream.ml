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

module BasicStream :> BASIC_STREAM =
struct
  type 'a stream = Stream of unit -> 'a front
  and 'a front = Empty | Cons of 'a * 'a stream

  fun delay (d) = Stream(d)
  fun expose (Stream(d)) = d ()

  let empty = Stream (fn () => Empty)
  fun cons (x, s) = Stream (fn () => Cons (x, s))
end;

(* Note that this implementation is NOT semantically *)
(* equivalent to the plain (non-memoizing) streams, since *)
(* effects will be executed only once in this implementation *)
module BasicMemoStream :> BASIC_STREAM =
struct

  type 'a stream = Stream of unit -> 'a front
  and 'a front = Empty | Cons of 'a * 'a stream

  exception Uninitialized

  fun expose (Stream (d)) = d ()
  fun delay (d) =
      let let memo = ref (fn () => raise Uninitialized)
	  fun memoFun () =
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
  fun cons (x, s) = Stream (fn () => Cons (x, s))
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

let recctor Stream
  (module BasicStream : BASIC_STREAM) :> STREAM =
struct
  open BasicStream

  exception EmptyStream

  (* functions null, hd, tl, map, filter, exists, take, drop *)
  (* parallel the functions in the List module *)
  fun null (s) = null' (expose s)
  and null' (Empty) = true
    | null' (Cons _) = false

  fun hd (s) = hd' (expose s)
  and hd' (Empty) = raise EmptyStream
    | hd' (Cons (x,s)) = x

  fun tl (s) = tl' (expose s)
  and tl' (Empty) = raise EmptyStream
    | tl' (Cons (x,s)) = s

  fun map f s = delay (fn () => map' f (expose s))
  and map' f (Empty) = Empty
    | map' f (Cons(x,s)) = Cons (f(x), map f s)

  fun filter p s = delay (fn () => filter' p (expose s))
  and filter' p (Empty) = Empty
    | filter' p (Cons(x,s)) =
        if p(x) then Cons (x, filter p s)
	else filter' p (expose s)

  fun exists p s = exists' p (expose s)
  and exists' p (Empty) = false
    | exists' p (Cons(x,s)) =
        p(x) orelse exists p s

  fun takePos (s, 0) = nil
    | takePos (s, n) = take' (expose s, n)
  and take' (Empty, _) = nil
    | take' (Cons(x,s), n) = x::takePos(s, n-1)

  fun take (s,n) = if n < 0 then raise Subscript else takePos (s,n)

  fun fromList (nil) = empty
    | fromList (x::l) = cons(x,fromList(l))

  fun toList (s) = toList' (expose s)
  and toList' (Empty) = nil
    | toList' (Cons(x,s)) = x::toList(s)

  fun dropPos (s, 0) = s
    | dropPos (s, n) = drop' (expose s, n)
  and drop' (Empty, _) = empty
    | drop' (Cons(x,s), n) = dropPos (s, n-1)

  fun drop (s,n) = if n < 0 then raise Subscript else dropPos (s,n)

  fun tabulate f = delay (fn () => tabulate' f)
  and tabulate' f = Cons (f(0), tabulate (fun i -> f(i+1)))

end;

(* module Stream :> STREAM --- non-memoizing *)
module Stream :> STREAM =
  Stream (module BasicStream = BasicStream);

(* module MStream :> STREAM --- memoizing *)
module MStream :> STREAM =
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
