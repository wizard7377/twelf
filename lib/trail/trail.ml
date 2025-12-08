(* Trailing Abstract Operations *)
(* Author: Roberto Virga *)

(Trail : TRAI)L =
struct

  local
    type 'a  Trail =
      Cons of 'a * 'a Trail
    | Mark of 'a Trail
    | Nil

    type 'a trail = 'a Trail ref

    fun trail () = ref Nil

    fun reset trail =
          trail := Nil


    fun suspend (trail, copy) =
      let
	fun suspend' Nil = Nil
(*	  | suspend' (Mark trail) = (Mark (suspend' trail))*)
	  | suspend' (Mark trail) = (suspend' trail)
	  | suspend' (Cons (action, trail)) =
	  Cons (copy action,  suspend' trail)
	let ftrail = suspend' (!trail)
      in
	ref ftrail
      end

    fun resume (ftrail, trail, reset) = 
      let
	fun resume' Nil = Nil
(*	  | resume' (Mark ftrail) = (Mark (resume' ftrail)) *)
	  | resume' (Mark ftrail) = resume' ftrail
	  | resume' (Cons (faction, ftrail)) = 
	  Cons (reset faction, resume' ftrail)
	let trail' = resume' (!ftrail)
      in 
       trail := trail'
      end 


    fun mark trail =
          trail := Mark (!trail)

    fun unwind (trail, undo) =
          let
            let rec unwind' = function Nil -> Nil
              | (Mark trail) -> trail
              | (Cons (action, trail)) -> 
                  (undo action ; unwind' trail)
          in
            trail := unwind' (!trail)
          end

    fun log (trail, action) =
          trail := Cons (action, !trail)

  in
    type 'a trail = 'a trail

    let trail = trail

    let suspend = suspend
    let resume = resume

    let reset = reset
    let mark = mark
    let unwind = unwind
    let log = log
  end (* local ... *)
end;; (* module Trail *)
