(* Printing Mode Declarations *)

(* Author: Carsten Schuermann *)

module type MODEPRINT = sig
  (*! structure ModeSyn : Modesyn.MODESYN !*)
  val modeToString : IntSyn.cid * ModeSyn.modeSpine -> string
  val modesToString : IntSyn.cid * ModeSyn.modeSpine list -> string
end

(* signature MODEPRINT *)
(* Printing Mode Declarations *)

(* Author: Carsten Schuermann *)

module ModePrint
    (Names : Names.NAMES)
    (Formatter : Formatter.FORMATTER)
    (Print : Print.PRINT) : MODEPRINT = struct
  (* structure ModeSyn = ModeSyn' *)

  module I = IntSyn
  module M = ModeSyn
  module F = Formatter
  module P = Print

  let rec modeToString = function
    | M.Plus -> "+"
    | M.Star -> "*"
    | M.Minus -> "-"
    | M.Minus1 -> "-1"

  let rec argToString (M.Marg (m, _)) = modeToString m

  let rec nameDec = function
    | I.Dec (_, V), M.Marg (_, name) -> I.Dec (name, V)
    | D, M.Marg (_, None) -> D

  let rec makeSpine G =
    let rec makeSpine' = function
      | I.Null, _, S -> S
      | I.Decl (G, _), k, S ->
          makeSpine' (G, k + 1, I.App (I.Root (I.BVar k, I.Nil), S))
    in
    makeSpine' (G, 1, I.Nil)

  let rec fmtModeDec (cid, mS) =
    let V = I.constType cid in
    let rec fmtModeDec' = function
      | G, _, M.Mnil ->
          [
            F.String "(";
            P.formatExp (G, I.Root (I.Const cid, makeSpine G));
            F.String ")";
          ]
      | G, I.Pi ((D, _), V'), M.Mapp (marg, S) ->
          let D' = nameDec (D, marg) in
          let D'' = Names.decEName (G, D') in
          [
            F.String (argToString marg);
            F.String "{";
            P.formatDec (G, D'');
            F.String "}";
            F.Break;
          ]
          @ fmtModeDec' (I.Decl (G, D''), V', S)
    in
    F.HVbox (fmtModeDec' (I.Null, V, mS))

  let rec fmtModeDecs = function
    | (cid, mS) :: [] -> fmtModeDec (cid, mS) :: []
    | (cid, mS) :: mdecs -> fmtModeDec (cid, mS) :: F.Break :: fmtModeDecs mdecs

  let rec modeToString cM = F.makestring_fmt (fmtModeDec cM)

  let rec modesToString mdecs =
    F.makestring_fmt (F.Vbox0 (0, 1, fmtModeDecs mdecs))

  let modeToString = modeToString
  let modesToString = modesToString
  (* local *)
end

(* functor ModePrint *)
