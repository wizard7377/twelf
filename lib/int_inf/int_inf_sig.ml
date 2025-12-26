open Basis ;; 

(* int-inf-sig.sml
 *
 * COPYRIGHT (c) 1995 by AT&T Bell Laboratories.  See COPYRIGHT file for_sml details.
 *
 * This package is derived from Andrzej Filinski's bignum package.  It is versy
 * close to the definition of the optional IntInf structure in the SML'97 basis.
 *)


module type INT_INF = sig
  include (module type of Integer)

  val divmod : int * int -> int * int
  val quotrem : int * int -> int * int
  val pow : int * int -> int
  val log2 : int -> int
end

(* signature INT_INF *)
