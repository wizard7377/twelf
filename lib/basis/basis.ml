module type TIME = sig
    type t ;;
    exception Time ;;
    val time : unit -> t ;;
    val zeroTime : t ;;
    val fromReal : float -> t ;;
    val toReal : t -> float ;;
    val toSeconds      : t -> int ;;
    val toMilliseconds : t -> int ;;
    val toMicroseconds : t -> int ;;
    val toNanoseconds  : t -> int ;;
    val fromSeconds      : int -> t ;;
    val fromMilliseconds : int -> t ;;
    val fromMicroseconds : int -> t ;;
    val fromNanoseconds  : int -> t ;;

    val (+) : t * t -> t ;;
    val (-) : t * t -> t ;;

    val compare : t * t -> int ;;
    val (<)  : t * t -> bool ;;
    val (<=) : t * t -> bool ;;
    val (>)  : t * t -> bool ;;
    val (>=) : t * t -> bool ;;

    val now : unit -> t ;;

    val fmt      : int -> t -> string ;;
    val toString : t -> string ;;
    val fromString : string -> t option  ;; 
end
(*
module Time : TIME = struct
    type t = Mtime.t ;;
    exception Time ;;
    let time () = Mtime_clock.now () ;;
    let zeroTime = Mtime.min_stamp ;;
    let fromNanoseconds f = Mtime.of_uint64_ns (Int64.of_int f) ;;
end
*)
