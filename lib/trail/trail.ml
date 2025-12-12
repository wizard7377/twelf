(* Trailing Abstract Operations *)
(* Author: Roberto Virga *)

structure Trail : TRAIL =
struct

  local
    datatype 'a  trail =
      Cons of 'a * 'a trail
    | Mark of 'a trail
    | Nil

    type 'a trail = 'a trail ref

    (* GEN BEGIN TAG INSIDE LET *) fun trail () = ref Nil (* GEN END TAG INSIDE LET *)

    (* GEN BEGIN TAG INSIDE LET *) fun reset trail =
          trail := Nil (* GEN END TAG INSIDE LET *)


    (* GEN BEGIN TAG INSIDE LET *) fun suspend (trail, copy) =
      let
    	fun suspend' Nil = Nil
    (*	  | suspend' (Mark trail) = (Mark (suspend' trail))*)
    	  | suspend' (Mark trail) = (suspend' trail)
    	  | suspend' (Cons (action, trail)) =
    	  Cons (copy action,  suspend' trail)
    	val ftrail = suspend' (!trail)
      in
    	ref ftrail
      end (* GEN END TAG INSIDE LET *)

    (* GEN BEGIN TAG INSIDE LET *) fun resume (ftrail, trail, reset) = 
      let
    	fun resume' Nil = Nil
    (*	  | resume' (Mark ftrail) = (Mark (resume' ftrail)) *)
    	  | resume' (Mark ftrail) = resume' ftrail
    	  | resume' (Cons (faction, ftrail)) = 
    	  Cons (reset faction, resume' ftrail)
    	val trail' = resume' (!ftrail)
      in 
       trail := trail'
      end (* GEN END TAG INSIDE LET *) 


    (* GEN BEGIN TAG INSIDE LET *) fun mark trail =
          trail := Mark (!trail) (* GEN END TAG INSIDE LET *)

    (* GEN BEGIN TAG INSIDE LET *) fun unwind (trail, undo) =
          let
            fun unwind' Nil = Nil
              | unwind' (Mark trail) = trail
              | unwind' (Cons (action, trail)) =
                  (undo action ; unwind' trail)
          in
            trail := unwind' (!trail)
          end (* GEN END TAG INSIDE LET *)

    (* GEN BEGIN TAG INSIDE LET *) fun log (trail, action) =
          trail := Cons (action, !trail) (* GEN END TAG INSIDE LET *)

  in
    type 'a trail = 'a trail

    (* GEN BEGIN TAG INSIDE LET *) val trail = trail (* GEN END TAG INSIDE LET *)

    (* GEN BEGIN TAG INSIDE LET *) val suspend = suspend (* GEN END TAG INSIDE LET *)
    (* GEN BEGIN TAG INSIDE LET *) val resume = resume (* GEN END TAG INSIDE LET *)

    (* GEN BEGIN TAG INSIDE LET *) val reset = reset (* GEN END TAG INSIDE LET *)
    (* GEN BEGIN TAG INSIDE LET *) val mark = mark (* GEN END TAG INSIDE LET *)
    (* GEN BEGIN TAG INSIDE LET *) val unwind = unwind (* GEN END TAG INSIDE LET *)
    (* GEN BEGIN TAG INSIDE LET *) val log = log (* GEN END TAG INSIDE LET *)
  end (* local ... *)
end; (* structure Trail *)
