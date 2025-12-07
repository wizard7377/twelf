(* Mode Table *)
(* Author: Carsten Schuermann *)
(* Modified: Frank Pfenning, Roberto Virga *)

let recctor ModeTable
  ((*! module IntSyn' : INTSYN !*)
   (* module Names : NAMES *)
   (*! sharing Names.IntSyn = IntSyn' !*)
   module Table : TABLE where type key = int): MODETABLE =
   (* module Index : INDEX *)
   (*! sharing Index.IntSyn = IntSyn' !*)
struct
  (*! module IntSyn = IntSyn' !*)
  exception Error of string

  local
    module I = IntSyn
    module M = ModeSyn

    let modeSignature : (M.ModeSpine list) Table.Table = Table.new(0);

    (* reset () = ()

       Effect: Resets mode array
    *)

    fun reset () = Table.clear modeSignature

    (* modeLookup a = mSOpt

       Looks up the mode of a in the mode array (if they are multiple, returns the last one
       inserted.
    *)
    fun modeLookup a =
          case (Table.lookup modeSignature a)
            of SOME (mS :: _) => SOME(mS)
             | NONE => NONE


    (* mmodeLookup a = mSs

       Looks up the modes of a in the mode array.
    *)
    fun mmodeLookup a =
          case (Table.lookup modeSignature a)
            of SOME mSs => mSs
             | NONE => nil


    (* installMode (a, mS) = ()

       Effect: the ModeSpine mS is stored with the type family a; if there were previous
               modes stored with a, they are replaced by mS
    *)
    fun installMode (a, mS) =
          Table.insert modeSignature (a, [mS])

    (* uninstallMode a = true iff a was declared in mode table
       Effect: the mode stored with a is removed
    *)
    fun uninstallMode a =
        case modeLookup a
          of NONE => false
           | SOME _ => (Table.delete modeSignature a; true)

    (* installMmode (a, mS) = ()

       Effect: the ModeSpine mS is stored with the type family a; if there were previous
               models stored with a, the new mode mS is added to them.
    *)
    fun installMmode (a, mS) =
          let
            let mSs = mmodeLookup a
          in
            Table.insert modeSignature (a, mS :: mSs)
          end

  in
    let reset = reset

    let installMode = installMode
    let modeLookup = modeLookup
    let uninstallMode = uninstallMode

    let installMmode = installMmode
    let mmodeLookup = mmodeLookup
  end
end;  (* functor ModeTable *)
