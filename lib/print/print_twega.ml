(* Printing *)
(* Author: Frank Pfenning *)
(* Modified: Jeff Polakow *)

functor (* GEN BEGIN FUNCTOR DECL *) PrintTwega
  ((*! structure IntSyn' : INTSYN !*)
   structure Whnf : WHNF
   (*! sharing Whnf.IntSyn = IntSyn' !*)
   structure Abstract : ABSTRACT
   (*! sharing Abstract.IntSyn = IntSyn' !*)
   structure Constraints : CONSTRAINTS
   (*! sharing Constraints.IntSyn = IntSyn' !*)
   structure Names : NAMES
   (*! sharing Names.IntSyn = IntSyn' !*)
   structure Formatter' : FORMATTER)
  : PRINT_TWEGA =
struct

  (*! structure IntSyn = IntSyn' !*)
structure Formatter = Formatter'

local
  (* Shorthands *)
  structure I = IntSyn
  structure F = Formatter
  (* GEN BEGIN TAG OUTSIDE LET *) val Str = F.String (* GEN END TAG OUTSIDE LET *)
  fun Str0 (s, n) = F.String0 n s
  fun Name (x) = F.String ("\"" ^ x ^ "\"")
  fun Integer (n) = F.String (Int.toString n)

  fun sexp (fmts) = F.Hbox [Str "(", F.HVbox fmts, Str ")"]

  (* fmtCon (c) = "c" where the name is assigned according the the Name table
     maintained in the names module.
     FVar's are printed with a preceding "`" (backquote) character
  *)
  fun (* GEN BEGIN FUN FIRST *) fmtCon (G, I.BVar(n)) = sexp [Str "tw~bvar", F.Break, Integer n] (* GEN END FUN FIRST *)
    | (* GEN BEGIN FUN BRANCH *) fmtCon (G, I.Const(cid)) = sexp [Str "tw~const", F.Break, Integer cid] (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) fmtCon (G, I.Def(cid)) = sexp [Str "tw~def", F.Break, Integer cid] (* GEN END FUN BRANCH *)
    (* I.Skonst, I.FVar cases should be impossible *)

  (* fmtUni (L) = "L" *)
  fun (* GEN BEGIN FUN FIRST *) fmtUni (I.Type) = Str "tw*type" (* GEN END FUN FIRST *)
    | (* GEN BEGIN FUN BRANCH *) fmtUni (I.Kind) = Str "tw*kind" (* GEN END FUN BRANCH *)

  (* fmtExpW (G, (U, s)) = fmt

     format the expression U[s].

     Invariants:
       G is a "printing context" (names in it are unique, but
            types may be incorrect) approximating G'
       G'' |- U : V   G' |- s : G''  (so  G' |- U[s] : V[s])
       (U,s) in whnf
  *)
  fun (* GEN BEGIN FUN FIRST *) fmtExpW (G, (I.Uni(L), s)) = sexp [Str "tw~uni", F.Break, fmtUni L] (* GEN END FUN FIRST *)
    | (* GEN BEGIN FUN BRANCH *) fmtExpW (G, (I.Pi((D as I.Dec(_,V1),P),V2), s)) =
      (case P (* if Pi is dependent but anonymous, invent name here *)
         of I.Maybe => let
                         (* GEN BEGIN TAG OUTSIDE LET *) val D' = Names.decLUName (G, D) (* GEN END TAG OUTSIDE LET *) (* could sometimes be EName *)
                         (* GEN BEGIN TAG OUTSIDE LET *) val G' = I.Decl (G, D') (* GEN END TAG OUTSIDE LET *)
                       in
                         sexp [Str "tw~pi", F.Break, fmtDec (G, (D', s)),
                               F.Break, Str "tw*maybe", F.Break, fmtExp (G', (V2, I.dot1 s))]
                       end
          | I.No => let
                       (* GEN BEGIN TAG OUTSIDE LET *) val G' = I.Decl (G, D) (* GEN END TAG OUTSIDE LET *)
                    in
                      sexp [Str "tw~pi", F.Break, fmtDec (G, (D, s)),
                            F.Break, Str "tw*no", F.Break, fmtExp (G', (V2, I.dot1 s))]
                    end) (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) fmtExpW (G, (I.Root (H, S), s)) =
         sexp [Str "tw~root", F.Break, fmtCon (G, H),
               F.Break, fmtSpine (G, (S, s))] (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) fmtExpW (G, (I.Lam(D, U), s)) =
      let
        (* GEN BEGIN TAG OUTSIDE LET *) val D' = Names.decLUName (G, D) (* GEN END TAG OUTSIDE LET *)
        (* GEN BEGIN TAG OUTSIDE LET *) val G' = I.Decl (G, D') (* GEN END TAG OUTSIDE LET *)
      in
        sexp [Str "tw~lam", F.Break, fmtDec (G, (D', s)),
              F.Break, fmtExp (G', (U, I.dot1 s))]
      end (* GEN END FUN BRANCH *)
    (* I.EClo, I.Redex, I.EVar not possible *)

  and fmtExp (G, (U, s)) = fmtExpW (G, Whnf.whnf (U, s))

  (* fmtSpine (G, (S, s)) = fmts
     format spine S[s] at printing depth d, printing length l, in printing
     context G which approximates G', where G' |- S[s] is valid
  *)
  and (* GEN BEGIN FUN FIRST *) fmtSpine (G, (I.Nil, _)) = Str "tw*empty-spine" (* GEN END FUN FIRST *)
    | (* GEN BEGIN FUN BRANCH *) fmtSpine (G, (I.SClo (S, s'), s)) =
         fmtSpine (G, (S, I.comp(s',s))) (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) fmtSpine (G, (I.App(U, S), s)) =
         sexp [Str "tw~app", F.Break, fmtExp (G, (U, s)),
               F.Break, fmtSpine (G, (S, s))] (* GEN END FUN BRANCH *)

  and (* GEN BEGIN FUN FIRST *) fmtDec (G, (I.Dec (NONE, V), s)) =
        sexp [Str "tw~decl", F.Break, Str "nil", F.Break, fmtExp (G, (V, s))] (* GEN END FUN FIRST *)
    | (* GEN BEGIN FUN BRANCH *) fmtDec (G, (I.Dec (SOME(x), V), s)) =
        sexp [Str "tw~decl", F.Break, Name x, F.Break, fmtExp (G, (V, s))] (* GEN END FUN BRANCH *)

  (* fmtConDec (condec) = fmt
     formats a constant declaration (which must be closed and in normal form)

     This function prints the quantifiers and abstractions only if hide = false.
  *)
  fun (* GEN BEGIN FUN FIRST *) fmtConDec (I.ConDec (name, parent, imp, _, V, L)) =
      let
        (* GEN BEGIN TAG OUTSIDE LET *) val _ = Names.varReset IntSyn.Null (* GEN END TAG OUTSIDE LET *)
      in
        sexp [Str "tw~defConst", F.Space, Name (name), F.Break,
              Integer (imp), F.Break, fmtExp (I.Null, (V, I.id)),
              F.Break, fmtUni (L)]
      end (* GEN END FUN FIRST *)
    | (* GEN BEGIN FUN BRANCH *) fmtConDec (I.SkoDec (name, parent, imp, V, L)) =
      Str ("%% Skipping Skolem constant " ^ name ^ " %%") (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) fmtConDec (I.ConDef (name, parent, imp, U, V, L, _)) =
      let
        (* GEN BEGIN TAG OUTSIDE LET *) val _ = Names.varReset IntSyn.Null (* GEN END TAG OUTSIDE LET *)
      in
        sexp [Str "tw~defConst", F.Space, Name (name), F.Break,
              Integer (imp), F.Break, fmtExp (I.Null, (U, I.id)),
              F.Break, fmtExp (I.Null, (V, I.id)),
              F.Break, fmtUni (L)]
      end (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) fmtConDec (I.AbbrevDef (name, parent, imp, U, V, L)) =
      let
        (* GEN BEGIN TAG OUTSIDE LET *) val _ = Names.varReset IntSyn.Null (* GEN END TAG OUTSIDE LET *)
      in
        sexp [Str "tw~defConst", F.Space, Name (name), F.Break,
              Integer (imp), F.Break, fmtExp (I.Null, (U, I.id)),
              F.Break, fmtExp (I.Null, (V, I.id)),
              F.Break, fmtUni (L)]
      end (* GEN END FUN BRANCH *)

  (* fmtEqn assumes that G is a valid printing context *)
  fun fmtEqn (I.Eqn (G, U1, U2)) = (* print context?? *)
      sexp [Str "tw*eqn", F.Break, fmtExp (G, (U1, I.id)), F.Break, fmtExp (G, (U2, I.id))]

  (* fmtEqnName and fmtEqns do not assume that G is a valid printing
     context and will name or rename variables to make it so.
     fmtEqns should only be used for printing constraints.
  *)
  fun fmtEqnName (I.Eqn (G, U1, U2)) =
      fmtEqn (I.Eqn (Names.ctxLUName G, U1, U2))

in

  (* In the functions below, G must be a "printing context", that is,
     (a) unique names must be assigned to each declaration which may
         actually applied in the scope (typically, using Names.decName)
     (b) types need not be well-formed, since they are not used
  *)
  fun formatDec (G, D) = fmtDec (G, (D, I.id))
  fun formatExp (G, U) = fmtExp (G, (U, I.id))
  fun formatSpine (G, S) = fmtSpine (G, (S, I.id))
  fun formatConDec (condec) = fmtConDec (condec)
  fun formatEqn (E) = fmtEqn E

  fun decToString (G, D) = F.makestring_fmt (formatDec (G, D))
  fun expToString (G, U) = F.makestring_fmt (formatExp (G, U))
  fun conDecToString (condec) = F.makestring_fmt (formatConDec (condec))
  fun eqnToString (E) = F.makestring_fmt (formatEqn E)

  fun printSgn () =
      IntSyn.sgnApp ((* GEN BEGIN FUNCTION EXPRESSION *) fn (cid) => (print (F.makestring_fmt (formatConDec (IntSyn.sgnLookup cid)));
                                  print "\n") (* GEN END FUNCTION EXPRESSION *))


  fun printSgnToFile filename =
      let
        (* GEN BEGIN TAG OUTSIDE LET *) val file = TextIO.openOut filename (* GEN END TAG OUTSIDE LET *)
  
        (* GEN BEGIN TAG OUTSIDE LET *) val _ =       IntSyn.sgnApp ((* GEN BEGIN FUNCTION EXPRESSION *) fn (cid) => (TextIO.output (file, F.makestring_fmt (formatConDec (IntSyn.sgnLookup cid)));
                                  TextIO.output (file, "\n")) (* GEN END FUNCTION EXPRESSION *)) (* GEN END TAG OUTSIDE LET *)
        (* GEN BEGIN TAG OUTSIDE LET *) val _ = TextIO.closeOut file (* GEN END TAG OUTSIDE LET *)
  
      in
        ()
      end

end  (* local ... *)

end (* GEN END FUNCTOR DECL *)  (* functor Print *)
