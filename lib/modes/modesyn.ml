(* Mode Syntax *)
(* Author: Carsten Schuermann *)
(* Modified: Frank Pfenning, Roberto Virga *)

module type MODESYN =
sig

  (*! (IntSyn : INTSYN) !*)

  type mode = Plus | Star | Minus | Minus1
  type modeSpine = Mnil | Mapp of Marg * modeSpine
  and Marg = Marg of mode * string option

  let modeEqual : mode * mode -> bool
  let modeToString : mode -> string
end;; (* module type MODESYN *)


(ModeSyn : MODESY)N =
struct

  exception Error of string

  type mode = Plus | Star | Minus | Minus1
  type modeSpine = Mnil | Mapp of Marg * modeSpine
  and  Marg = Marg of mode * string option
   

  (* modeEqual (M1, M2) = true iff M1 = M2 *)
  fun modeEqual (Plus, Plus) = true
    | modeEqual (Star, Star) = true
    | modeEqual (Minus, Minus) = true
    | modeEqual (Minus1, Minus1) = true
    | modeEqual (_, _) = false

  (* modeToString M = string
    
       converts a mode into a string for error messages
  *)
  fun modeToString Plus = "input (+)"
    | modeToString Star = "unrestricted (*)"
    | modeToString Minus = "output (-)"
    | modeToString Minus1 = "unique output (-1)"

end;; (* module ModeSyn *)
