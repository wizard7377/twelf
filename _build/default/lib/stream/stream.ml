(* Stream Library *)
(* Author: Frank Pfenning *)

(* BASIC_STREAM defines the visible "core" of streams *)
(* GEN BEGIN SIGNATURE DECLARATION *) signature BASIC_STREAM =
sig
  type 'a stream
  datatype 'a front = Empty | Cons of 'a * 'a stream

  (* Lazy stream construction and exposure *)
  val delay : (unit -> 'a front) -> 'a stream
  val expose : 'a stream -> 'a front

  (* Eager stream construction *)
  val empty : 'a stream
  val cons : 'a * 'a stream -> 'a stream
end (* GEN END SIGNATURE DECLARATION *);

structure BasicStream :> BASIC_STREAM =
struct
  datatype 'a stream = Stream of unit -> 'a front
  and 'a front = Empty | Cons of 'a * 'a stream

  fun delay (d) = Stream(d)
  fun expose (Stream(d)) = d ()

  (* GEN BEGIN TAG OUTSIDE LET *) val empty = Stream ((* GEN BEGIN FUNCTION EXPRESSION *) fn () => Empty (* GEN END FUNCTION EXPRESSION *)) (* GEN END TAG OUTSIDE LET *)
  fun cons (x, s) = Stream ((* GEN BEGIN FUNCTION EXPRESSION *) (* GEN BEGIN FUNCTION EXPRESSION *) fn () => Cons (x, s) (* GEN END FUNCTION EXPRESSION *) (* GEN END FUNCTION EXPRESSION *))
end;

(* Note that this implementation is NOT semantically *)
(* equivalent to the plain (non-memoizing) streams, since *)
(* effects will be executed only once in this implementation *)
structure BasicMemoStream :> BASIC_STREAM =
struct

  datatype 'a stream = Stream of unit -> 'a front
  and 'a front = Empty | Cons of 'a * 'a stream

  exception Uninitialized

  fun expose (Stream (d)) = d ()
  fun delay (d) =
      let (* GEN BEGIN TAG OUTSIDE LET *) val memo = ref ((* GEN BEGIN FUNCTION EXPRESSION *) fn () => raise Uninitialized (* GEN END FUNCTION EXPRESSION *)) (* GEN END TAG OUTSIDE LET *)
  	  fun memoFun () =
  	      let
  		  (* GEN BEGIN TAG OUTSIDE LET *) val r = d () (* GEN END TAG OUTSIDE LET *)
  	       in
  		  ( memo := ((* GEN BEGIN FUNCTION EXPRESSION *) (* GEN BEGIN FUNCTION EXPRESSION *) fn () => r (* GEN END FUNCTION EXPRESSION *) (* GEN END FUNCTION EXPRESSION *)) ; r )
  	      end
  	      handle exn => ( memo := ((* GEN BEGIN FUNCTION EXPRESSION *) (* GEN BEGIN FUNCTION EXPRESSION *) fn () => raise exn (* GEN END FUNCTION EXPRESSION *) (* GEN END FUNCTION EXPRESSION *)) ; raise exn )
      in
  	memo := memoFun ; Stream ((* GEN BEGIN FUNCTION EXPRESSION *) (* GEN BEGIN FUNCTION EXPRESSION *) fn () => !memo () (* GEN END FUNCTION EXPRESSION *) (* GEN END FUNCTION EXPRESSION *))
      end

  (* GEN BEGIN TAG OUTSIDE LET *) val empty = Stream ((* GEN BEGIN FUNCTION EXPRESSION *) fn () => Empty (* GEN END FUNCTION EXPRESSION *)) (* GEN END TAG OUTSIDE LET *)
  fun cons (x, s) = Stream ((* GEN BEGIN FUNCTION EXPRESSION *) (* GEN BEGIN FUNCTION EXPRESSION *) fn () => Cons (x, s) (* GEN END FUNCTION EXPRESSION *) (* GEN END FUNCTION EXPRESSION *))
end;

(* STREAM extends BASIC_STREAMS by operations *)
(* definable without reference to the implementation *)
(* GEN BEGIN SIGNATURE DECLARATION *) signature STREAM =
sig
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
end (* GEN END SIGNATURE DECLARATION *);

functor (* GEN BEGIN FUNCTOR DECL *) (* GEN BEGIN FUNCTOR DECL *) Stream
  (structure BasicStream : BASIC_STREAM) :> STREAM =
struct
  open BasicStream

  exception EmptyStream

  (* functions null, hd, tl, map, filter, exists, take, drop *)
  (* parallel the functions in the List structure *)
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
  and tabulate' f = Cons (f(0), tabulate (fn i => f(i+1)))

end (* GEN END FUNCTOR DECL *) (* GEN END FUNCTOR DECL *);

(* structure Stream :> STREAM --- non-memoizing *)
structure Stream :> STREAM =
  Stream (structure BasicStream = BasicStream);

(* structure MStream :> STREAM --- memoizing *)
structure MStream :> STREAM =
  Stream (structure BasicStream = BasicMemoStream);

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
