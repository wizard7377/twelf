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

    fun trail () = ref Nil

    fun reset trail =
          trail := Nil


    fun suspend (trail, copy) =
      let
    	fun suspend' Nil = Nil
    (*	  | suspend' (Mark trail) = (Mark (suspend' trail))*)
    	  | (* GEN CASE BRANCH *) suspend' (Mark trail) = (suspend' trail)
    	  | (* GEN CASE BRANCH *) suspend' (Cons (action, trail)) =
    	  Cons (copy action,  suspend' trail)
    	val ftrail = suspend' (!trail)
      in
    	ref ftrail
      end

    fun resume (ftrail, trail, reset) = 
      let
    	fun resume' Nil = Nil
    (*	  | resume' (Mark ftrail) = (Mark (resume' ftrail)) *)
    	  | (* GEN CASE BRANCH *) resume' (Mark ftrail) = resume' ftrail
    	  | (* GEN CASE BRANCH *) resume' (Cons (faction, ftrail)) = 
    	  Cons (reset faction, resume' ftrail)
    	val trail' = resume' (!ftrail)
      in 
       trail := trail'
      end 


    fun mark trail =
          trail := Mark (!trail)

    fun unwind (trail, undo) =
          let
            fun unwind' Nil = Nil
              | (* GEN CASE BRANCH *) unwind' (Mark trail) = trail
              | (* GEN CASE BRANCH *) unwind' (Cons (action, trail)) =
                  (undo action ; unwind' trail)
          in
            trail := unwind' (!trail)
          end

    fun log (trail, action) =
          trail := Cons (action, !trail)

  in
    type 'a trail = 'a trail

    val trail = trail

    val suspend = suspend
    val resume = resume

    val reset = reset
    val mark = mark
    val unwind = unwind
    val log = log
  end (* local ... *)
end; (* structure Trail *)
