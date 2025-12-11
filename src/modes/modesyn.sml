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
    | (* GEN CASE BRANCH *) modeEqual (Star, Star) = true
    | (* GEN CASE BRANCH *) modeEqual (Minus, Minus) = true
    | (* GEN CASE BRANCH *) modeEqual (Minus1, Minus1) = true
    | (* GEN CASE BRANCH *) modeEqual (_, _) = false

  (* modeToString M = string
    
       converts a mode into a string for error messages
  *)
  fun modeToString Plus = "input (+)"
    | (* GEN CASE BRANCH *) modeToString Star = "unrestricted (*)"
    | (* GEN CASE BRANCH *) modeToString Minus = "output (-)"
    | (* GEN CASE BRANCH *) modeToString Minus1 = "unique output (-1)"

end;  (* structure ModeSyn *)
