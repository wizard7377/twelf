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
  fun cons (x, s) = Stream ((* GEN BEGIN FUNCTION EXPRESSION *) fn () => Cons (x, s) (* GEN END FUNCTION EXPRESSION *))
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
  		  ( memo := ((* GEN BEGIN FUNCTION EXPRESSION *) fn () => r (* GEN END FUNCTION EXPRESSION *)) ; r )
  	      end
  	      handle exn => ( memo := ((* GEN BEGIN FUNCTION EXPRESSION *) fn () => raise exn (* GEN END FUNCTION EXPRESSION *)) ; raise exn )
      in
  	memo := memoFun ; Stream ((* GEN BEGIN FUNCTION EXPRESSION *) fn () => !memo () (* GEN END FUNCTION EXPRESSION *))
      end

  (* GEN BEGIN TAG OUTSIDE LET *) val empty = Stream ((* GEN BEGIN FUNCTION EXPRESSION *) fn () => Empty (* GEN END FUNCTION EXPRESSION *)) (* GEN END TAG OUTSIDE LET *)
  fun cons (x, s) = Stream ((* GEN BEGIN FUNCTION EXPRESSION *) fn () => Cons (x, s) (* GEN END FUNCTION EXPRESSION *))
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

functor (* GEN BEGIN FUNCTOR DECL *) Stream
  (structure BasicStream : BASIC_STREAM) :> STREAM =
struct
  open BasicStream

  exception EmptyStream

  (* functions null, hd, tl, map, filter, exists, take, drop *)
  (* parallel the functions in the List structure *)
  fun null (s) = null' (expose s)
  and (* GEN BEGIN FUN FIRST *) null' (Empty) = true (* GEN END FUN FIRST *)
    | (* GEN BEGIN FUN BRANCH *) null' (Cons _) = false (* GEN END FUN BRANCH *)

  fun hd (s) = hd' (expose s)
  and (* GEN BEGIN FUN FIRST *) hd' (Empty) = raise EmptyStream (* GEN END FUN FIRST *)
    | (* GEN BEGIN FUN BRANCH *) hd' (Cons (x,s)) = x (* GEN END FUN BRANCH *)

  fun tl (s) = tl' (expose s)
  and (* GEN BEGIN FUN FIRST *) tl' (Empty) = raise EmptyStream (* GEN END FUN FIRST *)
    | (* GEN BEGIN FUN BRANCH *) tl' (Cons (x,s)) = s (* GEN END FUN BRANCH *)

  fun map f s = delay ((* GEN BEGIN FUNCTION EXPRESSION *) fn () => map' f (expose s) (* GEN END FUNCTION EXPRESSION *))
  and (* GEN BEGIN FUN FIRST *) map' f (Empty) = Empty (* GEN END FUN FIRST *)
    | (* GEN BEGIN FUN BRANCH *) map' f (Cons(x,s)) = Cons (f(x), map f s) (* GEN END FUN BRANCH *)

  fun filter p s = delay ((* GEN BEGIN FUNCTION EXPRESSION *) fn () => filter' p (expose s) (* GEN END FUNCTION EXPRESSION *))
  and (* GEN BEGIN FUN FIRST *) filter' p (Empty) = Empty (* GEN END FUN FIRST *)
    | (* GEN BEGIN FUN BRANCH *) filter' p (Cons(x,s)) =
        if p(x) then Cons (x, filter p s)
    	else filter' p (expose s) (* GEN END FUN BRANCH *)

  fun exists p s = exists' p (expose s)
  and (* GEN BEGIN FUN FIRST *) exists' p (Empty) = false (* GEN END FUN FIRST *)
    | (* GEN BEGIN FUN BRANCH *) exists' p (Cons(x,s)) =
        p(x) orelse exists p s (* GEN END FUN BRANCH *)

  fun (* GEN BEGIN FUN FIRST *) takePos (s, 0) = nil (* GEN END FUN FIRST *)
    | (* GEN BEGIN FUN BRANCH *) takePos (s, n) = take' (expose s, n) (* GEN END FUN BRANCH *)
  and (* GEN BEGIN FUN FIRST *) take' (Empty, _) = nil (* GEN END FUN FIRST *)
    | (* GEN BEGIN FUN BRANCH *) take' (Cons(x,s), n) = x::takePos(s, n-1) (* GEN END FUN BRANCH *)

  fun take (s,n) = if n < 0 then raise Subscript else takePos (s,n)

  fun (* GEN BEGIN FUN FIRST *) fromList (nil) = empty (* GEN END FUN FIRST *)
    | (* GEN BEGIN FUN BRANCH *) fromList (x::l) = cons(x,fromList(l)) (* GEN END FUN BRANCH *)

  fun toList (s) = toList' (expose s)
  and (* GEN BEGIN FUN FIRST *) toList' (Empty) = nil (* GEN END FUN FIRST *)
    | (* GEN BEGIN FUN BRANCH *) toList' (Cons(x,s)) = x::toList(s) (* GEN END FUN BRANCH *)

  fun (* GEN BEGIN FUN FIRST *) dropPos (s, 0) = s (* GEN END FUN FIRST *)
    | (* GEN BEGIN FUN BRANCH *) dropPos (s, n) = drop' (expose s, n) (* GEN END FUN BRANCH *)
  and (* GEN BEGIN FUN FIRST *) drop' (Empty, _) = empty (* GEN END FUN FIRST *)
    | (* GEN BEGIN FUN BRANCH *) drop' (Cons(x,s), n) = dropPos (s, n-1) (* GEN END FUN BRANCH *)

  fun drop (s,n) = if n < 0 then raise Subscript else dropPos (s,n)

  fun tabulate f = delay ((* GEN BEGIN FUNCTION EXPRESSION *) fn () => tabulate' f (* GEN END FUNCTION EXPRESSION *))
  and tabulate' f = Cons (f(0), tabulate ((* GEN BEGIN FUNCTION EXPRESSION *) fn i => f(i+1) (* GEN END FUNCTION EXPRESSION *)))

end (* GEN END FUNCTOR DECL *);

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
