(* Printing Signatures *)

(* Author: Frank Pfenning *)

(* modified: Carsten Schuermann *)

module type PRINT_XML = sig
  val printSgn : unit -> unit
  val printSgnToFile : string -> string -> unit
end

(* signature PRINT_XML *)
(* Printing *)

(* Author: Frank Pfenning *)

(* Modified: Jeff Polakow *)

(* Modified: Carsten Schuermann *)

module PrintXML
    (Whnf : WHNF)
    (Abstract : ABSTRACT)
    (Constraints : CONSTRAINTS)
    (Names : NAMES)
    (Formatter' : FORMATTER) : PRINT_XML = struct
  (*! structure IntSyn = IntSyn' !*)

  module Formatter = Formatter'
  (* Shorthands *)

  module I = IntSyn
  module F = Formatter

  let Str = F.String
  let rec (Str0 (s, n)) = F.string0 n s
  let rec (Name x) = F.String ("\"" ^ x ^ "\"")
  let rec (Integer n) = F.String ("\"" ^ Int.toString n ^ "\"")
  let rec sexp fmts = F.Hbox [ F.HVbox fmts ]
  (* fmtCon (c) = "c" where the name is assigned according the the Name table
     maintained in the names module.
     FVar's are printed with a preceding "`" (backquote) character
  *)

  let rec fmtCon = function
    | G, I.BVar n ->
        let (I.Dec (Some n, _)) = I.ctxDec (G, n) in
        sexp [ Str ("<Var name = \"" ^ n ^ "\"/>") ]
    | G, I.Const cid ->
        sexp
          [
            Str "<Const name=\"";
            Str (I.conDecName (I.sgnLookup cid));
            Str "\"/>";
          ]
    | G, I.Def cid -> sexp [ Str "<Def>"; F.Break; Integer cid; Str "</Def>" ]
    | G, I.FgnConst (csid, condec) -> sexp [ Str "FngConst" ]
  (* FIX -cs Fri Jan 28 17:45:35 2005*)

  (* I.Skonst, I.FVar cases should be impossible *)

  (* fmtUni (L) = "L" *)

  let rec fmtUni = function I.Type -> Str "<Type/>" | I.Kind -> Str "<Kind/>"
  (* fmtExpW (G, (U, s)) = fmt

     format the expression U[s].

     Invariants:
       G is a "printing context" (names in it are unique, but
            types may be incorrect) approximating G'
       G'' |- U : V   G' |- s : G''  (so  G' |- U[s] : V[s])
       (U,s) in whnf
  *)

  let rec fmtExpW = function
    | G, (I.Uni L, s) -> sexp [ Str "<Uni>"; F.Break; fmtUni L; Str "</Uni>" ]
    | G, (I.Pi ((D, P), V2), s) -> (
        match P (* if Pi is dependent but anonymous, invent name here *) with
        | I.Maybe ->
            (* could sometimes be EName *)
            let D' = Names.decLUName (G, D) in
            let G' = I.Decl (G, D') in
            sexp
              [
                Str "<Pi>";
                F.Break;
                fmtDec (G, (D', s));
                F.Break;
                (* Str "tw*maybe", F.Break, *)
                fmtExp (G', (V2, I.dot1 s));
                Str "</Pi>";
              ]
        | I.No ->
            let G' = I.Decl (G, D) in
            sexp
              [
                Str "<Arrow>";
                F.Break;
                fmtDec' (G, (D, s));
                F.Break;
                (* Str "tw*no", F.Break,*)
                fmtExp (G', (V2, I.dot1 s));
                Str "</Arrow>";
              ])
    | G, (I.Root (H, S), s) -> (
        match fmtSpine (G, (S, s)) with
        | None -> fmtCon (G, H)
        | Some fmts ->
            F.HVbox
              [ Str "<App>"; fmtCon (G, H); F.Break; sexp fmts; Str "</App>" ])
    | G, (I.Lam (D, U), s) ->
        let D' = Names.decLUName (G, D) in
        let G' = I.Decl (G, D') in
        sexp
          [
            Str "<Lam>";
            F.Break;
            fmtDec (G, (D', s));
            F.Break;
            fmtExp (G', (U, I.dot1 s));
            Str "</Lam>";
          ]
    | G, (I.FgnExp (csid, F), s) -> sexp [ Str "FgnExp" ]

  and fmtExp (G, (U, s)) = fmtExpW (G, Whnf.whnf (U, s))

  and fmtSpine = function
    | G, (I.Nil, _) -> None
    | G, (I.SClo (S, s'), s) -> fmtSpine (G, (S, I.comp (s', s)))
    | G, (I.App (U, S), s) -> (
        match fmtSpine (G, (S, s)) with
        | None -> Some [ fmtExp (G, (U, s)) ]
        | Some fmts -> Some ([ fmtExp (G, (U, s)); F.Break ] @ fmts))

  and fmtDec = function
    | G, (I.Dec (None, V), s) ->
        sexp [ Str "<Dec>"; F.Break; fmtExp (G, (V, s)); Str "</Dec>" ]
    | G, (I.Dec (Some x, V), s) ->
        sexp
          [
            Str "<Dec name =";
            Name x;
            Str ">";
            F.Break;
            fmtExp (G, (V, s));
            Str "</Dec>";
          ]

  and fmtDec' = function
    | G, (I.Dec (None, V), s) -> sexp [ fmtExp (G, (V, s)) ]
    | G, (I.Dec (Some x, V), s) -> sexp [ fmtExp (G, (V, s)) ]
  (* fmtConDec (condec) = fmt
     formats a constant declaration (which must be closed and in normal form)

     This function prints the quantifiers and abstractions only if hide = false.
  *)

  let rec fmtConDec = function
    | I.ConDec (name, parent, imp, _, V, L) ->
        let _ = Names.varReset IntSyn.Null in
        sexp
          [
            Str "<Condec name=";
            Name name;
            F.Break;
            Str "implicit=";
            Integer imp;
            Str ">";
            F.Break;
            fmtExp (I.Null, (V, I.id));
            F.Break;
            fmtUni L;
            Str "</Condec>";
          ]
    | I.SkoDec (name, parent, imp, V, L) ->
        Str ("<! Skipping Skolem constant " ^ name ^ ">")
    | I.ConDef (name, parent, imp, U, V, L, _) ->
        let _ = Names.varReset IntSyn.Null in
        sexp
          [
            Str "<Condef name=";
            Name name;
            F.Break;
            Str "implicit=";
            Integer imp;
            Str ">";
            F.Break;
            fmtExp (I.Null, (U, I.id));
            F.Break;
            fmtExp (I.Null, (V, I.id));
            F.Break;
            fmtUni L;
            Str "</Condef>";
          ]
    | I.AbbrevDef (name, parent, imp, U, V, L) ->
        let _ = Names.varReset IntSyn.Null in
        sexp
          [
            Str "<Abbrevdef name=";
            Name name;
            Str ">";
            F.Break;
            Integer imp;
            F.Break;
            fmtExp (I.Null, (U, I.id));
            F.Break;
            fmtExp (I.Null, (V, I.id));
            F.Break;
            fmtUni L;
            Str "</Abbrevdef>";
          ]
    | I.BlockDec (name, _, _, _) ->
        Str ("<! Skipping Skolem constant " ^ name ^ ">")
  (* fmtEqn assumes that G is a valid printing context *)

  let rec fmtEqn (I.Eqn (G, U1, U2)) =
    (* print context?? *)
    sexp
      [
        Str "<Equation>";
        F.Break;
        fmtExp (G, (U1, I.id));
        F.Break;
        fmtExp (G, (U2, I.id));
        Str "</Equation>";
      ]
  (* fmtEqnName and fmtEqns do not assume that G is a valid printing
     context and will name or rename variables to make it so.
     fmtEqns should only be used for_sml printing constraints.
  *)

  let rec fmtEqnName (I.Eqn (G, U1, U2)) =
    fmtEqn (I.Eqn (Names.ctxLUName G, U1, U2))
  (* In the functions below, G must be a "printing context", that is,
     (a) unique names must be assigned to each declaration which may
         actually applied in the scope (typically, using Names.decName)
     (b) types need not be well-formed, since they are not used
  *)

  let rec formatDec (G, D) = fmtDec (G, (D, I.id))
  let rec formatExp (G, U) = fmtExp (G, (U, I.id))
  (*  fun formatSpine (G, S) = sexp (fmtSpine (G, (S, I.id))) *)

  let rec formatConDec condec = fmtConDec condec
  let rec formatEqn E = fmtEqn E
  let rec decToString (G, D) = F.makestring_fmt (formatDec (G, D))
  let rec expToString (G, U) = F.makestring_fmt (formatExp (G, U))
  let rec conDecToString condec = F.makestring_fmt (formatConDec condec)
  let rec eqnToString E = F.makestring_fmt (formatEqn E)

  let rec printSgn () =
    IntSyn.sgnApp (fun cid ->
        print (F.makestring_fmt (formatConDec (IntSyn.sgnLookup cid)));
        print "\n")

  let rec printSgnToFile path filename =
    let file = TextIO.openOut (path ^ filename) in
    let _ =
      TextIO.output
        ( file,
          "<?xml version=\"1.0\" encoding=\"UTF-8\"?>\n\
           <!-- nsgmls ex.xml -->\n\
           <!DOCTYPE Signature SYSTEM \"lf.dtd\">\n\
           <Signature>" )
    in
    let _ =
      IntSyn.sgnApp (fun cid ->
          TextIO.output
            (file, F.makestring_fmt (formatConDec (IntSyn.sgnLookup cid)));
          TextIO.output (file, "\n"))
    in
    let _ = TextIO.output (file, "</Signature>") in
    let _ = TextIO.closeOut file in
    ()
  (* local ... *)
end

(* functor PrintXml *)
