(* GEN BEGIN SIGNATURE DECLARATION *) signature MSG =
sig
    val message : string -> unit
    val setMessageFunc : (string -> unit) -> unit
end (* GEN END SIGNATURE DECLARATION *)

structure Msg :> MSG =
struct
 (* GEN BEGIN TAG OUTSIDE LET *) val default = print (* GEN END TAG OUTSIDE LET *) 
 (* GEN BEGIN TAG OUTSIDE LET *) val messageFunc = ref (default) (* GEN END TAG OUTSIDE LET *)
 fun setMessageFunc f = (messageFunc := f)
 fun message s = ((!messageFunc) s)
end
