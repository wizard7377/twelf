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
  fun (* GEN BEGIN FUN FIRST *) modeEqual (Plus, Plus) = true (* GEN END FUN FIRST *)
    | (* GEN BEGIN FUN BRANCH *) modeEqual (Star, Star) = true (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) modeEqual (Minus, Minus) = true (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) modeEqual (Minus1, Minus1) = true (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) modeEqual (_, _) = false (* GEN END FUN BRANCH *)

  (* modeToString M = string
    
       converts a mode into a string for error messages
  *)
  fun (* GEN BEGIN FUN FIRST *) modeToString Plus = "input (+)" (* GEN END FUN FIRST *)
    | (* GEN BEGIN FUN BRANCH *) modeToString Star = "unrestricted (*)" (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) modeToString Minus = "output (-)" (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) modeToString Minus1 = "unique output (-1)" (* GEN END FUN BRANCH *)

end;  (* structure ModeSyn *)
