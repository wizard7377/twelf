(* Mode Syntax *)
(* Author: Carsten Schuermann *)
(* Modified: Frank Pfenning, Roberto Virga *)

signature MODESYN =
sig

  (*! structure IntSyn : INTSYN !*)

  datatype mode = Plus | Star | Minus | Minus1
  datatype mode_spine = Mnil | Mapp of marg * mode_spine
  and marg = Marg of mode * string option

  val modeEqual : mode * mode -> bool
  val modeToString : mode -> string
end;  (* signature MODESYN *)


structure ModeSyn :> MODESYN =
struct

  exception Error of string

  datatype mode = Plus | Star | Minus | Minus1
  datatype mode_spine = Mnil | Mapp of marg * mode_spine
  and  marg = Marg of mode * string option
   

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

end;  (* structure ModeSyn *)
