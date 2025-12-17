PrintTwega  Whnf WHNF    Abstract ABSTRACT    Constraints CONSTRAINTS    Names NAMES    Formatter' FORMATTER     PRINT_TWEGA  struct (*! structure IntSyn = IntSyn' !*)
module (* Shorthands *)
module module let  inlet rec str0(s,  , n) string0 n slet rec name(x) string ("\"" ^ x ^ "\"")let rec integer(n) string (toString n)let rec sexp(fmts) hbox [str "("; hVbox fmts; str ")"](* fmtCon (c) = "c" where the name is assigned according the the Name table
     maintained in the names module.
     FVar's are printed with a preceding "`" (backquote) character
  *)
let rec fmtCon(g,  , bVar (n)) sexp [str "tw~bvar"; break; integer n] fmtCon(g,  , const (cid)) sexp [str "tw~const"; break; integer cid] fmtCon(g,  , def (cid)) sexp [str "tw~def"; break; integer cid](* I.Skonst, I.FVar cases should be impossible *)
(* fmtUni (L) = "L" *)
let rec fmtUni(type) str "tw*type" fmtUni(kind) str "tw*kind"(* fmtExpW (G, (U, s)) = fmt

     format the expression U[s].

     Invariants:
       G is a "printing context" (names in it are unique, but
            types may be incorrect) approximating G'
       G'' |- U : V   G' |- s : G''  (so  G' |- U[s] : V[s])
       (U,s) in whnf
  *)
let rec fmtExpW(g,  , (uni (l),  , s)) sexp [str "tw~uni"; break; fmtUni l] fmtExpW(g,  , (pi ((d as dec (_,  , v1),  , p),  , v2),  , s)) (match p(* if Pi is dependent but anonymous, invent name here *)
 with maybe -> let let  in(* could sometimes be EName *)
let  in in sexp [str "tw~pi"; break; fmtDec (g,  , (d',  , s)); break; str "tw*maybe"; break; fmtExp (g',  , (v2,  , dot1 s))] no -> let let  in in sexp [str "tw~pi"; break; fmtDec (g,  , (d,  , s)); break; str "tw*no"; break; fmtExp (g',  , (v2,  , dot1 s))]) fmtExpW(g,  , (root (h,  , s),  , s)) sexp [str "tw~root"; break; fmtCon (g,  , h); break; fmtSpine (g,  , (s,  , s))] fmtExpW(g,  , (lam (d,  , u),  , s)) let let  inlet  in in sexp [str "tw~lam"; break; fmtDec (g,  , (d',  , s)); break; fmtExp (g',  , (u,  , dot1 s))](* I.EClo, I.Redex, I.EVar not possible *)
 fmtExp(g,  , (u,  , s)) fmtExpW (g,  , whnf (u,  , s))(* fmtSpine (G, (S, s)) = fmts
     format spine S[s] at printing depth d, printing length l, in printing
     context G which approximates G', where G' |- S[s] is valid
  *)
 fmtSpine(g,  , (nil,  , _)) str "tw*empty-spine" fmtSpine(g,  , (sClo (s,  , s'),  , s)) fmtSpine (g,  , (s,  , comp (s',  , s))) fmtSpine(g,  , (app (u,  , s),  , s)) sexp [str "tw~app"; break; fmtExp (g,  , (u,  , s)); break; fmtSpine (g,  , (s,  , s))] fmtDec(g,  , (dec (nONE,  , v),  , s)) sexp [str "tw~decl"; break; str "nil"; break; fmtExp (g,  , (v,  , s))] fmtDec(g,  , (dec (sOME (x),  , v),  , s)) sexp [str "tw~decl"; break; name x; break; fmtExp (g,  , (v,  , s))](* fmtConDec (condec) = fmt
     formats a constant declaration (which must be closed and in normal form)

     This function prints the quantifiers and abstractions only if hide = false.
  *)
let rec fmtConDec(conDec (name,  , parent,  , imp,  , _,  , v,  , l)) let let  in in sexp [str "tw~defConst"; space; name (name); break; integer (imp); break; fmtExp (null,  , (v,  , id)); break; fmtUni (l)] fmtConDec(skoDec (name,  , parent,  , imp,  , v,  , l)) str ("%% Skipping Skolem constant " ^ name ^ " %%") fmtConDec(conDef (name,  , parent,  , imp,  , u,  , v,  , l,  , _)) let let  in in sexp [str "tw~defConst"; space; name (name); break; integer (imp); break; fmtExp (null,  , (u,  , id)); break; fmtExp (null,  , (v,  , id)); break; fmtUni (l)] fmtConDec(abbrevDef (name,  , parent,  , imp,  , u,  , v,  , l)) let let  in in sexp [str "tw~defConst"; space; name (name); break; integer (imp); break; fmtExp (null,  , (u,  , id)); break; fmtExp (null,  , (v,  , id)); break; fmtUni (l)](* fmtEqn assumes that G is a valid printing context *)
let rec fmtEqn(eqn (g,  , u1,  , u2)) sexp [str "tw*eqn"; break; fmtExp (g,  , (u1,  , id)); break; fmtExp (g,  , (u2,  , id))](* fmtEqnName and fmtEqns do not assume that G is a valid printing
     context and will name or rename variables to make it so.
     fmtEqns should only be used for printing constraints.
  *)
let rec fmtEqnName(eqn (g,  , u1,  , u2)) fmtEqn (eqn (ctxLUName g,  , u1,  , u2))(* In the functions below, G must be a "printing context", that is,
     (a) unique names must be assigned to each declaration which may
         actually applied in the scope (typically, using Names.decName)
     (b) types need not be well-formed, since they are not used
  *)
let rec formatDec(g,  , d) fmtDec (g,  , (d,  , id))let rec formatExp(g,  , u) fmtExp (g,  , (u,  , id))let rec formatSpine(g,  , s) fmtSpine (g,  , (s,  , id))let rec formatConDec(condec) fmtConDec (condec)let rec formatEqn(e) fmtEqn elet rec decToString(g,  , d) makestring_fmt (formatDec (g,  , d))let rec expToString(g,  , u) makestring_fmt (formatExp (g,  , u))let rec conDecToString(condec) makestring_fmt (formatConDec (condec))let rec eqnToString(e) makestring_fmt (formatEqn e)let rec printSgn() sgnApp (fun (cid) -> (print (makestring_fmt (formatConDec (sgnLookup cid))); print "\n"))let rec printSgnToFilefilename let let  inlet  inlet  in in ()(* local ... *)
end