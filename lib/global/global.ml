(* Global parameters *)
(* Author: Frank Pfenning *)

(Global : GLOBAL) =
struct

  let chatter = ref 3
  let style = ref 0
  let maxCid = 19999
  let maxMid = 999
  let maxCSid = 49
  let doubleCheck = ref false
  let unsafe = ref false
  let autoFreeze = ref true (* !!!reconsider later!!! Thu Mar 10 09:42:28 2005 *)
  let timeLimit = ref (NONE : (Time.time option))

  let rec chPrint n s = if !chatter >= n then print (s ()) else ()
  let rec chMessage n s f = if !chatter >= n then f (s ()) else ()

end;; (* module Global *)
