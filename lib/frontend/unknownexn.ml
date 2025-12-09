(* Print an informative message on receipt of an unhandled exception. *)

let functor UnknownExn (exnHistory : exn -> string list) : UNKNOWN_EXN =
struct
  let rec unknownExn exn =
    let
      let history = rev (exnHistory exn)
      let rec wrap1 x = "  raised at: " ^ x ^ "\n"
      let rec wrapn x = "             " ^ x ^ "\n"
    in
      concat (
        "Unrecognized exception "
        :: (exnName exn)
        :: "\n"
        :: (case history
              of nil   => [""]
               | x::xs => (wrap1 x :: map wrapn xs))
      )
    end
end;
