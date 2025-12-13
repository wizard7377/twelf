(* Printing Mode Declarations *)
(* Author: Carsten Schuermann *)

functor (* GEN BEGIN FUNCTOR DECL *) ModePrint ((*! structure ModeSyn' : MODESYN !*)
                   structure Names : NAMES
                   (*! sharing Names.IntSyn = ModeSyn'.IntSyn !*)
                   structure Formatter : FORMATTER
                   structure Print : PRINT
                   (*! sharing Print.IntSyn = ModeSyn'.IntSyn !*)
                     sharing Print.Formatter = Formatter)
  : MODEPRINT =
struct
  (* structure ModeSyn = ModeSyn' *)

  local
    structure I = IntSyn
    structure M = ModeSyn
    structure F = Formatter
    structure P = Print

    fun (* GEN BEGIN FUN FIRST *) modeToString M.Plus = "+" (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) modeToString M.Star = "*" (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) modeToString M.Minus = "-" (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) modeToString M.Minus1 = "-1" (* GEN END FUN BRANCH *)

    fun argToString (M.Marg (m, _)) = modeToString m

    fun (* GEN BEGIN FUN FIRST *) nameDec (I.Dec (_, V) , M.Marg (_, name as SOME _)) = I.Dec (name, V) (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) nameDec (D, M.Marg (_, NONE)) = D (* GEN END FUN BRANCH *)

    fun makeSpine (G) =
        let
          fun (* GEN BEGIN FUN FIRST *) makeSpine' (I.Null, _, S) = S (* GEN END FUN FIRST *)
            | (* GEN BEGIN FUN BRANCH *) makeSpine' (I.Decl (G, _), k, S) =
                makeSpine' (G, k+1, I.App (I.Root (I.BVar k, I.Nil), S)) (* GEN END FUN BRANCH *)
        in
          makeSpine' (G, 1, I.Nil)
        end

    fun fmtModeDec (cid, mS) =
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val V = I.constType cid (* GEN END TAG OUTSIDE LET *)
          fun (* GEN BEGIN FUN FIRST *) fmtModeDec' (G, _, M.Mnil) =
                [F.String "(",
                 P.formatExp (G, I.Root (I.Const (cid), makeSpine G)),
                 F.String ")"] (* GEN END FUN FIRST *)
            | (* GEN BEGIN FUN BRANCH *) fmtModeDec' (G, I.Pi ((D, _), V'), M.Mapp (marg, S)) =
                let
                  (* GEN BEGIN TAG OUTSIDE LET *) val D' = nameDec (D, marg) (* GEN END TAG OUTSIDE LET *)
                  (* GEN BEGIN TAG OUTSIDE LET *) val D'' = Names.decEName (G, D') (* GEN END TAG OUTSIDE LET *)
                in
                  [F.String (argToString marg), F.String "{", P.formatDec (G, D''),
                   F.String "}", F.Break] @ (fmtModeDec' (I.Decl (G, D''), V', S))
                end (* GEN END FUN BRANCH *)
        in
          F.HVbox (fmtModeDec' (I.Null, V, mS))
        end

    fun (* GEN BEGIN FUN FIRST *) fmtModeDecs ((cid, mS)::nil) = fmtModeDec (cid, mS)::nil (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) fmtModeDecs ((cid, mS)::mdecs) =
        fmtModeDec (cid, mS)::F.Break::fmtModeDecs mdecs (* GEN END FUN BRANCH *)

    fun modeToString cM = F.makestring_fmt (fmtModeDec cM)
    fun modesToString mdecs = F.makestring_fmt (F.Vbox0 0 1 (fmtModeDecs mdecs))
  in
    (* GEN BEGIN TAG OUTSIDE LET *) val modeToString = modeToString (* GEN END TAG OUTSIDE LET *)
    (* GEN BEGIN TAG OUTSIDE LET *) val modesToString = modesToString (* GEN END TAG OUTSIDE LET *)
  end (* local *)

end (* GEN END FUNCTOR DECL *); (* functor ModePrint *)
