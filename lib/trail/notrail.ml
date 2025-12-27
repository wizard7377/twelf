open Basis

(* Not Trailing Abstract Operations *)

(* Author: Roberto Virga *)
open Trail

module NoTrail : TRAIL = struct
  type 'a trail = unit

  let trail () = ref ()
  let suspend (_, _copy) = ()
  let resume (_, _, _reset) = ()
  let reset _ = ()
  let mark _ = ()
  let unwind (_, _undo) = ()
  let log (_, _action) = ()
end

(* structure NoTrail *)
