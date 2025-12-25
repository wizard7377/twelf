open Basis ;; 
(* Mode Table *)

(* Author: Frank Pfenning *)

module type MODETABLE = sig
  exception Error of string

  val reset : unit -> unit

  (* single mode installation and lookup *)
  val installMode : IntSyn.cid * ModeSyn.modeSpine -> unit
  val modeLookup : IntSyn.cid -> ModeSyn.modeSpine option
  val uninstallMode : IntSyn.cid -> bool

  (* true: was declared, false: not *)
  (* multiple mode installation and lookup *)
  val installMmode : IntSyn.cid * ModeSyn.modeSpine -> unit
  val mmodeLookup : IntSyn.cid -> ModeSyn.modeSpine list
end

(* signature MODETABLE *)
(* Mode Table *)

(* Author: Carsten Schuermann *)

(* Modified: Frank Pfenning, Roberto Virga *)

module ModeTable : MODETABLE = struct
  (*! structure IntSyn = IntSyn' !*)

  exception Error of string

  module I = IntSyn
  module M = ModeSyn

  let modeSignature : M.modeSpine list Table.table = Table.new_ 0
  (* reset () = ()

       Effect: Resets mode array
    *)

  let rec reset () = Table.clear modeSignature
  (* modeLookup a = mSOpt

       Looks up the mode of a in the mode array (if they are multiple, returns the last one
       inserted.
    *)

  let rec modeLookup a =
    match Table.lookup modeSignature a with
    | Some (mS :: _) -> Some mS
    | None -> None
  (* mmodeLookup a = mSs

       Looks up the modes of a in the mode array.
    *)

  let rec mmodeLookup a =
    match Table.lookup modeSignature a with Some mSs -> mSs | None -> []
  (* installMode (a, mS) = ()

       Effect: the ModeSpine mS is stored with the type family a; if there were previous
               modes stored with a, they are replaced by mS
    *)

  let rec installMode (a, mS) = Table.insert modeSignature (a, [ mS ])
  (* uninstallMode a = true iff a was declared in mode table
       Effect: the mode stored with a is removed
    *)

  let rec uninstallMode a =
    match modeLookup a with
    | None -> false
    | Some _ ->
        Table.delete modeSignature a;
        true
  (* installMmode (a, mS) = ()

       Effect: the ModeSpine mS is stored with the type family a; if there were previous
               models stored with a, the new mode mS is added to them.
    *)

  let rec installMmode (a, mS) =
    let mSs = mmodeLookup a in
    Table.insert modeSignature (a, mS :: mSs)

  let reset = reset
  let installMode = installMode
  let modeLookup = modeLookup
  let uninstallMode = uninstallMode
  let installMmode = installMmode
  let mmodeLookup = mmodeLookup
end

(* functor ModeTable *)
