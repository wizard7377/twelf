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
    	fun (* GEN BEGIN CASE FIRST *) (* GEN BEGIN CASE FIRST *) suspend' Nil = Nil (* GEN END CASE FIRST *) (* GEN END CASE FIRST *)
    (*	  | suspend' (Mark trail) = (Mark (suspend' trail))*)
    	  | (* GEN BEGIN CASE BRANCH *) suspend' (Mark trail) = (suspend' trail) (* GEN END CASE BRANCH *)
    	  | (* GEN BEGIN CASE BRANCH *) (* GEN BEGIN CASE BRANCH *) suspend' (Cons (action, trail)) =
    	  Cons (copy action,  suspend' trail) (* GEN END CASE BRANCH *) (* GEN END CASE BRANCH *)
    	(* GEN BEGIN TAG OUTSIDE LET *) val ftrail = suspend' (!trail) (* GEN END TAG OUTSIDE LET *)
      in
    	ref ftrail
      end

    fun resume (ftrail, trail, reset) = 
      let
    	fun (* GEN BEGIN CASE FIRST *) (* GEN BEGIN CASE FIRST *) resume' Nil = Nil (* GEN END CASE FIRST *) (* GEN END CASE FIRST *)
    (*	  | resume' (Mark ftrail) = (Mark (resume' ftrail)) *)
    	  | (* GEN BEGIN CASE BRANCH *) resume' (Mark ftrail) = resume' ftrail (* GEN END CASE BRANCH *)
    	  | (* GEN BEGIN CASE BRANCH *) (* GEN BEGIN CASE BRANCH *) resume' (Cons (faction, ftrail)) = 
    	  Cons (reset faction, resume' ftrail) (* GEN END CASE BRANCH *) (* GEN END CASE BRANCH *)
    	(* GEN BEGIN TAG OUTSIDE LET *) val trail' = resume' (!ftrail) (* GEN END TAG OUTSIDE LET *)
      in 
       trail := trail'
      end 


    fun mark trail =
          trail := Mark (!trail)

    fun unwind (trail, undo) =
          let
            fun (* GEN BEGIN CASE FIRST *) (* GEN BEGIN CASE FIRST *) unwind' Nil = Nil (* GEN END CASE FIRST *) (* GEN END CASE FIRST *)
              | (* GEN BEGIN CASE BRANCH *) unwind' (Mark trail) = trail (* GEN END CASE BRANCH *)
              | (* GEN BEGIN CASE BRANCH *) (* GEN BEGIN CASE BRANCH *) unwind' (Cons (action, trail)) =
                  (undo action ; unwind' trail) (* GEN END CASE BRANCH *) (* GEN END CASE BRANCH *)
          in
            trail := unwind' (!trail)
          end

    fun log (trail, action) =
          trail := Cons (action, !trail)

  in
    type 'a trail = 'a trail

    (* GEN BEGIN TAG OUTSIDE LET *) val trail = trail (* GEN END TAG OUTSIDE LET *)

    (* GEN BEGIN TAG OUTSIDE LET *) val suspend = suspend (* GEN END TAG OUTSIDE LET *)
    (* GEN BEGIN TAG OUTSIDE LET *) val resume = resume (* GEN END TAG OUTSIDE LET *)

    (* GEN BEGIN TAG OUTSIDE LET *) val reset = reset (* GEN END TAG OUTSIDE LET *)
    (* GEN BEGIN TAG OUTSIDE LET *) val mark = mark (* GEN END TAG OUTSIDE LET *)
    (* GEN BEGIN TAG OUTSIDE LET *) val unwind = unwind (* GEN END TAG OUTSIDE LET *)
    (* GEN BEGIN TAG OUTSIDE LET *) val log = log (* GEN END TAG OUTSIDE LET *)
  end (* local ... *)
end; (* structure Trail *)
