(* Printing *)
(* Author: Frank Pfenning *)
(* Modified: Jeff Polakow *)

module PrintTwega
  ((*! module IntSyn' : INTSYN !*)
   (Whnf : WHNF)
   (*! sharing Whnf.IntSyn = IntSyn' !*)
   (Abstract : ABSTRACT)
   (*! sharing Abstract.IntSyn = IntSyn' !*)
   (Constraints : CONSTRAINTS)
   (*! sharing Constraints.IntSyn = IntSyn' !*)
   (Names : NAMES)
   (*! sharing Names.IntSyn = IntSyn' !*)
   module Formatter' : FORMATTER)
  : PRINT_TWEGA =
struct

  (*! module IntSyn = IntSyn' !*)
module Formatter = Formatter'

local
  (* Shorthands *)
  module I = IntSyn
  module F = Formatter
  let Str = F.String
  let rec Str0 (s, n) = F.String0 n s
  let rec Name (x) = F.String ("\"" ^ x ^ "\"")
  let rec Integer (n) = F.String (Int.toString n)

  let rec sexp (fmts) = F.Hbox [Str "(", F.HVbox fmts, Str ")"]

  (* fmtCon (c) = "c" where the name is assigned according the the Name table
     maintained in the names module.
     FVar's are printed with a preceding "`" (backquote) character
  *)
  let rec fmtCon = function (G, I.BVar(n)) -> sexp [Str "tw~bvar", F.Break, Integer n]
    | (G, I.Const(cid)) -> sexp [Str "tw~const", F.Break, Integer cid]
    | (G, I.Def(cid)) -> sexp [Str "tw~def", F.Break, Integer cid]
    (* I.Skonst, I.FVar cases should be impossible *)

  (* fmtUni (L) = "L" *)
  let rec fmtUni = function (I.Type) -> Str "tw*type"
    | (I.Kind) -> Str "tw*kind"

  (* fmtExpW (G, (U, s)) = fmt

     format the expression U[s].

     Invariants:
       G is a "printing context" (names in it are unique, but
            types may be incorrect) approximating G'
       G'' |- U : V   G' |- s : G''  (so  G' |- U[s] : V[s])
       (U,s) in whnf
  *)
  let rec fmtExpW = function (G, (I.Uni(L), s)) -> sexp [Str "tw~uni", F.Break, fmtUni L]
    | (G, (I.Pi((D as I.Dec(_,V1),P),V2), s)) -> 
      (case P (* if Pi is dependent but anonymous, invent name here *)
         of I.Maybe => let
                         let D' = Names.decLUName (G, D) (* could sometimes be EName *)
                         let G' = I.Decl (G, D')
                       in
                         sexp [Str "tw~pi", F.Break, fmtDec (G, (D', s)),
                               F.Break, Str "tw*maybe", F.Break, fmtExp (G', (V2, I.dot1 s))]
                       end
          | I.No => let
                       let G' = I.Decl (G, D)
                    in
                      sexp [Str "tw~pi", F.Break, fmtDec (G, (D, s)),
                            F.Break, Str "tw*no", F.Break, fmtExp (G', (V2, I.dot1 s))]
                    end)
    | (G, (I.Root (H, S), s)) -> 
         sexp [Str "tw~root", F.Break, fmtCon (G, H),
               F.Break, fmtSpine (G, (S, s))]
    | (G, (I.Lam(D, U), s)) -> 
      let
        let D' = Names.decLUName (G, D)
        let G' = I.Decl (G, D')
      in
        sexp [Str "tw~lam", F.Break, fmtDec (G, (D', s)),
              F.Break, fmtExp (G', (U, I.dot1 s))]
      end
    (* I.EClo, I.Redex, I.EVar not possible *)

  and fmtExp (G, (U, s)) = fmtExpW (G, Whnf.whnf (U, s))

  (* fmtSpine (G, (S, s)) = fmts
     format spine S[s] at printing depth d, printing length l, in printing
     context G which approximates G', where G' |- S[s] is valid
  *)
  and fmtSpine (G, (I.Nil, _)) = Str "tw*empty-spine"
    | fmtSpine (G, (I.SClo (S, s'), s)) =
         fmtSpine (G, (S, I.comp(s',s)))
    | fmtSpine (G, (I.App(U, S), s)) =
         sexp [Str "tw~app", F.Break, fmtExp (G, (U, s)),
               F.Break, fmtSpine (G, (S, s))]

  and fmtDec (G, (I.Dec (NONE, V), s)) =
        sexp [Str "tw~decl", F.Break, Str "nil", F.Break, fmtExp (G, (V, s))]
    | fmtDec (G, (I.Dec (SOME(x), V), s)) =
        sexp [Str "tw~decl", F.Break, Name x, F.Break, fmtExp (G, (V, s))]

  (* fmtConDec (condec) = fmt
     formats a constant declaration (which must be closed and in normal form)

     This function prints the quantifiers and abstractions only if hide = false.
  *)
  let rec fmtConDec = function (I.ConDec (name, parent, imp, _, V, L)) -> 
      let
        let _ = Names.varReset IntSyn.Null
      in
        sexp [Str "tw~defConst", F.Space, Name (name), F.Break,
              Integer (imp), F.Break, fmtExp (I.Null, (V, I.id)),
              F.Break, fmtUni (L)]
      end
    | (I.SkoDec (name, parent, imp, V, L)) -> 
      Str ("%% Skipping Skolem constant " ^ name ^ " %%")
    | (I.ConDef (name, parent, imp, U, V, L, _)) -> 
      let
        let _ = Names.varReset IntSyn.Null
      in
        sexp [Str "tw~defConst", F.Space, Name (name), F.Break,
              Integer (imp), F.Break, fmtExp (I.Null, (U, I.id)),
              F.Break, fmtExp (I.Null, (V, I.id)),
              F.Break, fmtUni (L)]
      end
    | (I.AbbrevDef (name, parent, imp, U, V, L)) -> 
      let
        let _ = Names.varReset IntSyn.Null
      in
        sexp [Str "tw~defConst", F.Space, Name (name), F.Break,
              Integer (imp), F.Break, fmtExp (I.Null, (U, I.id)),
              F.Break, fmtExp (I.Null, (V, I.id)),
              F.Break, fmtUni (L)]
      end

  (* fmtEqn assumes that G is a valid printing context *)
  let rec fmtEqn (I.Eqn (G, U1, U2)) = (* print context?? *)
      sexp [Str "tw*eqn", F.Break, fmtExp (G, (U1, I.id)), F.Break, fmtExp (G, (U2, I.id))]

  (* fmtEqnName and fmtEqns do not assume that G is a valid printing
     context and will name or rename variables to make it so.
     fmtEqns should only be used for printing constraints.
  *)
  let rec fmtEqnName (I.Eqn (G, U1, U2)) =
      fmtEqn (I.Eqn (Names.ctxLUName G, U1, U2))

in

  (* In the functions below, G must be a "printing context", that is,
     (a) unique names must be assigned to each declaration which may
         actually applied in the scope (typically, using Names.decName)
     (b) types need not be well-formed, since they are not used
  *)
  let rec formatDec (G, D) = fmtDec (G, (D, I.id))
  let rec formatExp (G, U) = fmtExp (G, (U, I.id))
  let rec formatSpine (G, S) = fmtSpine (G, (S, I.id))
  let rec formatConDec (condec) = fmtConDec (condec)
  let rec formatEqn (E) = fmtEqn E

  let rec decToString (G, D) = F.makestring_fmt (formatDec (G, D))
  let rec expToString (G, U) = F.makestring_fmt (formatExp (G, U))
  let rec conDecToString (condec) = F.makestring_fmt (formatConDec (condec))
  let rec eqnToString (E) = F.makestring_fmt (formatEqn E)

  let rec printSgn () =
      IntSyn.sgnApp (fn (cid) => (print (F.makestring_fmt (formatConDec (IntSyn.sgnLookup cid)));
                                  print "\n"))


  let rec printSgnToFile filename =
      let
        let file = TextIO.openOut filename

        let _ =       IntSyn.sgnApp (fn (cid) => (TextIO.output (file, F.makestring_fmt (formatConDec (IntSyn.sgnLookup cid)));
                                  TextIO.output (file, "\n")))
        let _ = TextIO.closeOut file

      in
        ()
      end

end  (* local ... *)

end  (* functor Print *)
