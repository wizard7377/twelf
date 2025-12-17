ModeTable  Table TABLE   Key Int     MODETABLE  struct (*! structure IntSyn = IntSyn' !*)
exception module module let  in(* reset () = ()

       Effect: Resets mode array
    *)
let rec reset() clear modeSignature(* modeLookup a = mSOpt

       Looks up the mode of a in the mode array (if they are multiple, returns the last one
       inserted.
    *)
let rec modeLookupa match (lookup modeSignature a) with sOME (mS :: _) -> sOME (mS) nONE -> nONE(* mmodeLookup a = mSs

       Looks up the modes of a in the mode array.
    *)
let rec mmodeLookupa match (lookup modeSignature a) with sOME mSs -> mSs nONE -> nil(* installMode (a, mS) = ()

       Effect: the ModeSpine mS is stored with the type family a; if there were previous
               modes stored with a, they are replaced by mS
    *)
let rec installMode(a,  , mS) insert modeSignature (a,  , [mS])(* uninstallMode a = true iff a was declared in mode table
       Effect: the mode stored with a is removed
    *)
let rec uninstallModea match modeLookup a with nONE -> false sOME _ -> (delete modeSignature a; true)(* installMmode (a, mS) = ()

       Effect: the ModeSpine mS is stored with the type family a; if there were previous
               models stored with a, the new mode mS is added to them.
    *)
let rec installMmode(a,  , mS) let let  in in insert modeSignature (a,  , mS :: mSs)let  inlet  inlet  inlet  inlet  inlet  inend