(* GEN BEGIN SIGNATURE DECLARATION *) signature MSG =
sig
    val message : string -> unit
    val setMessageFunc : (string -> unit) -> unit
end (* GEN END SIGNATURE DECLARATION *)

structure Msg :> MSG =
struct
 (* GEN BEGIN TAG INSIDE LET *) val default = print (* GEN END TAG INSIDE LET *) 
 (* GEN BEGIN TAG INSIDE LET *) val messageFunc = ref (default) (* GEN END TAG INSIDE LET *)
 (* GEN BEGIN TAG INSIDE LET *) fun setMessageFunc f = (messageFunc := f) (* GEN END TAG INSIDE LET *)
 (* GEN BEGIN TAG INSIDE LET *) fun message s = ((!messageFunc) s) (* GEN END TAG INSIDE LET *)
end
