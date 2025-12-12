(* Mode Syntax *)
(* Author: Carsten Schuermann *)
(* Modified: Frank Pfenning, Roberto Virga *)

(* GEN BEGIN SIGNATURE DECLARATION *) signature MODESYN =
sig

  (*! structure IntSyn : INTSYN !*)

  datatype mode = Plus | Star | Minus | Minus1
  datatype mode_spine = Mnil | Mapp of marg * mode_spine
  and marg = Marg of mode * string option

  val modeEqual : mode * mode -> bool
  val modeToString : mode -> string
end (* GEN END SIGNATURE DECLARATION *);  (* signature MODESYN *)


structure ModeSyn :> MODESYN =
struct

  exception Error of string

  datatype mode = Plus | Star | Minus | Minus1
  datatype mode_spine = Mnil | Mapp of marg * mode_spine
  and  marg = Marg of mode * string option
   

  (* modeEqual (M1, M2) = true iff M1 = M2 *)
  (* GEN BEGIN TAG INSIDE LET *) fun modeEqual (Plus, Plus) = true
    | modeEqual (Star, Star) = true
    | modeEqual (Minus, Minus) = true
    | modeEqual (Minus1, Minus1) = true
    | modeEqual (_, _) = false (* GEN END TAG INSIDE LET *)

  (* modeToString M = string
    
       converts a mode into a string for error messages
  *)
  (* GEN BEGIN TAG INSIDE LET *) fun modeToString Plus = "input (+)"
    | modeToString Star = "unrestricted (*)"
    | modeToString Minus = "output (-)"
    | modeToString Minus1 = "unique output (-1)" (* GEN END TAG INSIDE LET *)

end;  (* structure ModeSyn *)
