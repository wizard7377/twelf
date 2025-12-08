(* Printing Mode Declarations *)
(* Author: Carsten Schuermann *)

module ModePrint ((*! module ModeSyn' : MODESYN !*)
                   (Names : NAMES)
                   (*! sharing Names.IntSyn = ModeSyn'.IntSyn !*)
                   (Formatter : FORMATTER)
                   (Print : PRINT)
                   (*! sharing Print.IntSyn = ModeSyn'.IntSyn !*)
                     sharing Print.Formatter = Formatter)
  : MODEPRINT =
struct
  (* module ModeSyn = ModeSyn' *)

  local
    module I = IntSyn
    module M = ModeSyn
    module F = Formatter
    module P = Print

    let rec modeToString = function M.Plus -> "+"
      | M.Star -> "*"
      | M.Minus -> "-"
      | M.Minus1 -> "-1"

    fun argToString (M.Marg (m, _)) = modeToString m

    let rec nameDec = function (I.Dec (_, V) , M.Marg (_, name as SOME _)) -> I.Dec (name, V)
      | (D, M.Marg (_, NONE)) -> D

    fun makeSpine (G) =
        let
          let rec makeSpine' = function (I.Null, _, S) -> S
            | (I.Decl (G, _), k, S) -> 
                makeSpine' (G, k+1, I.App (I.Root (I.BVar k, I.Nil), S))
        in
          makeSpine' (G, 1, I.Nil)
        end

    fun fmtModeDec (cid, mS) =
        let
          let V = I.constType cid
          let rec fmtModeDec' = function (G, _, M.Mnil) -> 
                [F.String "(",
                 P.formatExp (G, I.Root (I.Const (cid), makeSpine G)),
                 F.String ")"]
            | (G, I.Pi ((D, _), V'), M.Mapp (marg, S)) -> 
                let
                  let D' = nameDec (D, marg)
                  let D'' = Names.decEName (G, D')
                in
                  [F.String (argToString marg), F.String "{", P.formatDec (G, D''),
                   F.String "}", F.Break] @ (fmtModeDec' (I.Decl (G, D''), V', S))
                end
        in
          F.HVbox (fmtModeDec' (I.Null, V, mS))
        end

    let rec fmtModeDecs = function ((cid, mS)::nil) -> fmtModeDec (cid, mS)::nil
      | ((cid, mS)::mdecs) -> 
        fmtModeDec (cid, mS)::F.Break::fmtModeDecs mdecs

    fun modeToString cM = F.makestring_fmt (fmtModeDec cM)
    fun modesToString mdecs = F.makestring_fmt (F.Vbox0 0 1 (fmtModeDecs mdecs))
  in
    let modeToString = modeToString
    let modesToString = modesToString
  end (* local *)

end;; (* functor ModePrint *)
