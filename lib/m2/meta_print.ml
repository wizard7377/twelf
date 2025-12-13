(* Meta printer for proof states *)
(* Author: Carsten Schuermann *)

functor (* GEN BEGIN FUNCTOR DECL *) MetaPrint (structure Global : GLOBAL
                   structure MetaSyn' : METASYN
                   structure Formatter : FORMATTER
                   structure Print : PRINT
                   (*! sharing Print.IntSyn = MetaSyn'.IntSyn !*)
                     sharing Print.Formatter = Formatter
                   structure ClausePrint : CLAUSEPRINT
                   (*! sharing ClausePrint.IntSyn = MetaSyn'.IntSyn !*)
                     sharing ClausePrint.Formatter = Formatter)

  : METAPRINT =
struct
  structure MetaSyn = MetaSyn'

  local
    structure M = MetaSyn
    structure I = IntSyn
    structure F = Formatter

    fun (* GEN BEGIN FUN FIRST *) modeToString M.Top = "+" (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) modeToString M.Bot = "-" (* GEN END FUN BRANCH *)

    (* depthToString is used to format splitting depth *)
    fun depthToString (b) = if b <= 0 then "" else Int.toString b

    fun fmtPrefix (GM) =
        let
          fun (* GEN BEGIN FUN FIRST *) fmtPrefix' (M.Prefix (I.Null, I.Null, I.Null), Fmt) = Fmt (* GEN END FUN FIRST *)
            | (* GEN BEGIN FUN BRANCH *) fmtPrefix' (M.Prefix (I.Decl (I.Null, D), I.Decl (I.Null, mode),
                                    I.Decl (I.Null, b)), Fmt) =
                [F.String (depthToString b),
                 F.String (modeToString mode),
                 Print.formatDec (I.Null, D)] @ Fmt (* GEN END FUN BRANCH *)
            | (* GEN BEGIN FUN BRANCH *) fmtPrefix' (M.Prefix (I.Decl (G, D), I.Decl (M, mode), I.Decl (B, b)), Fmt) =
                fmtPrefix' (M.Prefix (G, M, B),
                            [F.String ",", F.Space, F.Break,
                             F.String (depthToString b),
                             F.String (modeToString mode),
                             Print.formatDec (G, D)] @ Fmt) (* GEN END FUN BRANCH *)
        in
          F.HVbox (fmtPrefix' (GM, []))
        end

    fun prefixToString GM = F.makestring_fmt (fmtPrefix GM)

    fun stateToString (M.State (name, GM as M.Prefix (G, M, B), V)) =
          name ^ ":\n"
          ^ prefixToString GM ^ "\n--------------\n"
          ^ ClausePrint.clauseToString (G, V) ^ "\n\n"

    fun (* GEN BEGIN FUN FIRST *) sgnToString (M.SgnEmpty) = "" (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) sgnToString (M.ConDec (e, S)) =
        (if !Global.chatter >= 4
           (* use explicitly quantified form *)
           then Print.conDecToString e ^ "\n"
         else
           if !Global.chatter >= 3
             (* use form without quantifiers, which is reparsable *)
             then ClausePrint.conDecToString e ^ "\n"
           else "")
        ^ sgnToString S (* GEN END FUN BRANCH *)
  in

    (* GEN BEGIN TAG OUTSIDE LET *) val modeToString = modeToString (* GEN END TAG OUTSIDE LET *)
    (* GEN BEGIN TAG OUTSIDE LET *) val sgnToString = sgnToString (* GEN END TAG OUTSIDE LET *)
    (* GEN BEGIN TAG OUTSIDE LET *) val stateToString = stateToString (* GEN END TAG OUTSIDE LET *)
    (* GEN BEGIN TAG OUTSIDE LET *) val conDecToString = ClausePrint.conDecToString (* GEN END TAG OUTSIDE LET *)

  end (* local *)
end (* GEN END FUNCTOR DECL *); (* functor MetaPrint *)
