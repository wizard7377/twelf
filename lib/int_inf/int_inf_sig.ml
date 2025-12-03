(* int-inf-sig.sml
 *
 * COPYRIGHT (c) 1995 by AT&T Bell Laboratories.  See COPYRIGHT file for details.
 *
 * This package is derived from Andrzej Filinski's bignum package.  It is versy
 * close to the definition of the optional IntInf module in the SML'97 basis.
 *)

module type INT_INF =
  sig
    include INTEGER

    let divmod  : (int * int) -> (int * int)
    let quotrem : (int * int) -> (int * int)
    let pow : (int * Int.int) -> int
    let log2 : int -> Int.int

  end (* module type INT_INF *)

