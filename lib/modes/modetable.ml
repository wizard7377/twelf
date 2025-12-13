(* Mode Table *)
(* Author: Carsten Schuermann *)
(* Modified: Frank Pfenning, Roberto Virga *)

functor (* GEN BEGIN FUNCTOR DECL *) ModeTable
  ((*! structure IntSyn' : INTSYN !*)
   (* structure Names : NAMES *)
   (*! sharing Names.IntSyn = IntSyn' !*)
   structure Table : TABLE where type key = int
   (* structure Index : INDEX *)
   (*! sharing Index.IntSyn = IntSyn' !*)
   ) : MODETABLE =
struct
  (*! structure IntSyn = IntSyn' !*)
  exception Error of string

  local
    structure I = IntSyn
    structure M = ModeSyn

    (* GEN BEGIN TAG OUTSIDE LET *) val modeSignature : (M.mode_spine list) Table.table = Table.new(0) (* GEN END TAG OUTSIDE LET *);

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
            (* GEN BEGIN TAG OUTSIDE LET *) val mSs = mmodeLookup a (* GEN END TAG OUTSIDE LET *)
          in
            Table.insert modeSignature (a, mS :: mSs)
          end

  in
    (* GEN BEGIN TAG OUTSIDE LET *) val reset = reset (* GEN END TAG OUTSIDE LET *)

    (* GEN BEGIN TAG OUTSIDE LET *) val installMode = installMode (* GEN END TAG OUTSIDE LET *)
    (* GEN BEGIN TAG OUTSIDE LET *) val modeLookup = modeLookup (* GEN END TAG OUTSIDE LET *)
    (* GEN BEGIN TAG OUTSIDE LET *) val uninstallMode = uninstallMode (* GEN END TAG OUTSIDE LET *)

    (* GEN BEGIN TAG OUTSIDE LET *) val installMmode = installMmode (* GEN END TAG OUTSIDE LET *)
    (* GEN BEGIN TAG OUTSIDE LET *) val mmodeLookup = mmodeLookup (* GEN END TAG OUTSIDE LET *)
  end
end (* GEN END FUNCTOR DECL *);  (* functor ModeTable *)
