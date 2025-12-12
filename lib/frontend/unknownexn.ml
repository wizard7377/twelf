(* Print an informative message on receipt of an unhandled exception. *)

functor (* GEN BEGIN FUNCTOR DECL *) UnknownExn (val exnHistory : exn -> string list) : UNKNOWN_EXN =
struct
  fun unknownExn exn =
    let
      val history = rev (exnHistory exn)
      fun wrap1 x = "  raised at: " ^ x ^ "\n"
      fun wrapn x = "             " ^ x ^ "\n"
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
end (* GEN END FUNCTOR DECL *);
