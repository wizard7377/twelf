(* Trailing Abstract Operations *)
(* Author: Roberto Virga *)

(Trail : TRAIL) =
struct

  local
    type 'a  Trail =
      Cons of 'a * 'a Trail
    | Mark of 'a Trail
    | Nil

    type 'a trail = 'a Trail ref

    let rec trail () = ref Nil

    let rec reset trail =
          trail := Nil


    let rec suspend (trail, copy) =
      let
	let rec suspend' Nil = Nil
(*	  | suspend' (Mark trail) = (Mark (suspend' trail))*)
	  | suspend' (Mark trail) = (suspend' trail)
	  | suspend' (Cons (action, trail)) =
	  Cons (copy action,  suspend' trail)
	let ftrail = suspend' (!trail)
      in
	ref ftrail
      end

    let rec resume (ftrail, trail, reset) = 
      let
	let rec resume' Nil = Nil
(*	  | resume' (Mark ftrail) = (Mark (resume' ftrail)) *)
	  | resume' (Mark ftrail) = resume' ftrail
	  | resume' (Cons (faction, ftrail)) = 
	  Cons (reset faction, resume' ftrail)
	let trail' = resume' (!ftrail)
      in 
       trail := trail'
      end 


    let rec mark trail =
          trail := Mark (!trail)

    let rec unwind (trail, undo) =
          let
            let rec unwind' = function Nil -> Nil
              | (Mark trail) -> trail
              | (Cons (action, trail)) -> 
                  (undo action ; unwind' trail)
          in
            trail := unwind' (!trail)
          end

    let rec log (trail, action) =
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
