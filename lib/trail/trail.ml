(* Trailing Abstract Operations *)


(* Author: Roberto Virga *)


module Trail : TRAIL = struct type 'a trail = Cons of 'a * 'a trail | Mark of 'a trail | Nil
type 'a trail = 'a trail ref
let rec trail ()  = ref Nil
let rec reset trail  = trail := Nil
let rec suspend (trail, copy)  = ( let rec suspend' = function Nil -> Nil | (Mark trail) -> (suspend' trail) | (Cons (action, trail)) -> Cons (copy action, suspend' trail) in let ftrail = suspend' (! trail) in  ref ftrail )
let rec resume (ftrail, trail, reset)  = ( let rec resume' = function Nil -> Nil | (Mark ftrail) -> resume' ftrail | (Cons (faction, ftrail)) -> Cons (reset faction, resume' ftrail) in let trail' = resume' (! ftrail) in  trail := trail' )
let rec mark trail  = trail := Mark (! trail)
let rec unwind (trail, undo)  = ( let rec unwind' = function Nil -> Nil | (Mark trail) -> trail | (Cons (action, trail)) -> (undo action; unwind' trail) in  trail := unwind' (! trail) )
let rec log (trail, action)  = trail := Cons (action, ! trail)
type 'a trail = 'a trail
let trail = trail
let suspend = suspend
let resume = resume
let reset = reset
let mark = mark
let unwind = unwind
let log = log
(* local ... *)

 end


(* structure Trail *)

