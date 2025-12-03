(* Delphin Frontend *)
(* Author: Carsten Schuermann *)

module type  DELPHIN =
sig
  val version : string
  val loadFile : string * string -> unit
    
  val top : unit -> unit

  val runSimpleTest : string -> (string list) -> string list -> unit
  val eval : Tomega.Prg -> Tomega.Prg
end
