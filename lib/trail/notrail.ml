(* Not Trailing Abstract Operations *)
(* Author: Roberto Virga *)

module NoTrail : TRAIL =
struct

  type 'a trail = unit

  fun trail () = ()

  fun suspend ((), copy) = ()
  fun resume ((),(), reset) = ()
  
  fun reset () = ()

  fun mark () = ()

  fun unwind ((), undo) = ()

  fun log ((), action) = ()
end; (* module NoTrail *)
