PrintOMDoc  Whnf WHNF    Abstract ABSTRACT    Constraints CONSTRAINTS    Names NAMES    Formatter' FORMATTER     PRINT_OMDOC  struct (*! structure IntSyn = IntSyn' !*)
module (* Shorthands *)
module (* The Formatter isn't really helpful for OMDoc output. So the basic functions are reimplemented here.
     indent : current indentatioin width
     nl_ind()() : newline and indent
     nl_unind()() : newline and unindent
     nl() : newline (with current indentation) *)
let  inlet  inlet rec tabs(n) if (n <= 0) then "" else tabstring ^ tabs (n - 1)let rec ind_reset() (indent := 0)let rec ind(n) indent := ! indent + nlet rec unind(n) indent := ! indent - nlet rec nl_ind() (indent := ! indent + 1; "\n" ^ tabs (! indent))let rec nl_unind() (indent := ! indent - 1; "\n" ^ tabs (! indent))let rec nl() "\n" ^ tabs (! indent)let rec escapes let let rec escapelistnil nil escapelist('&' :: rest) explode "&amp;" @ (escapelist rest) escapelist('<' :: rest) explode "&lt;" @ (escapelist rest) escapelist('>' :: rest) explode "&gt;" @ (escapelist rest) escapelist(c :: rest) c :: (escapelist rest) in implode (escapelist (explode s))(* If namesafe is true during printing, the output is guaranteed to be namesafe (no duplicate names).
    But it doesn't look good. If the user knows that are no overloaded constants, namesafe can be set to false. *)
let  in(* XML start characters: ":" | "_" | [A-Z] | [a-z], further characters: "-" | "." | [0-9] *)
let rec replacec if (isAlphaNum c) || (contains ":_-." c) then (str c) else "_"let rec name(cid) let let  inlet  inlet  in in if (! namesafe) then start ^ name ^ "__c" ^ (toString cid) else n(* x must be the number of the varialbe in left ro right order in the context *)
let rec varName(x,  , n) let let  inlet  in in if (! namesafe) then start ^ name ^ "__v" ^ (toString x) else n(* Some original Formatter functions replaced with trivial functions. *)
(* val Str  = F.String
  fun Str0 (s, n) = F.String0 n s
  fun Integer (n) = ("\"" ^ Int.toString n ^ "\"") *)
let rec str(s) s(* fun sexp (fmts) = F.Hbox [F.HVbox fmts] *)
let rec sexp(l) concat l(* This is probably defined elsewhere, too. It's needed to check how many arguments there will be in an om:OMA element *)
let rec spineLengthnil 0 spineLength(sClo (s,  , _)) spineLength s spineLength(app (_,  , s)) 1 + (spineLength s)(* fmtCon (c) = "c" where the name is assigned according the the Name table
     maintained in the names module.
     FVar's are printed with a preceding "`" (backquote) character
  *)
let rec fmtCon(g,  , bVar (x)) let let  in in sexp [str ("<om:OMV name=\"" ^ varName (ctxLength g - x + 1,  , n) ^ "\"/>")] fmtCon(g,  , const (cid)) sexp [str "<om:OMS cd=\"global\" name=\""; name cid; str "\"/>"] fmtCon(g,  , def (cid)) sexp [str "<om:OMS cd=\"global\" name=\""; name cid; str "\"/>"] fmtCon(g,  , fgnConst (csid,  , condec)) sexp [str "FgnConst"](* FIX -cs Fri Jan 28 17:45:35 2005*)
(* I.Skonst, I.FVar cases should be impossible *)
(* fmtUni (L) = "L" *)
let rec fmtUni(type) str "<om:OMS cd=\"twelf\" name=\"type\"/>" fmtUni(kind) str "<om:OMS cd=\"twelf\" name=\"kind\"/>"(* fmtExpW (G, (U, s)) = fmt

     format the expression U[s].

     Invariants:
       G is a "printing context" (names in it are unique, but
            types may be incorrect) approximating G'
       G'' |- U : V   G' |- s : G''  (so  G' |- U[s] : V[s])
       (U,s) in whnf
  *)
let rec fmtExpW(g,  , (uni (l),  , s),  , _) sexp [fmtUni l] fmtExpW(g,  , (pi ((d as dec (_,  , v1),  , p),  , v2),  , s),  , imp) (match p(* if Pi is dependent but anonymous, invent name here *)
 with maybe -> let let  in(* could sometimes be EName *)
let  inlet  in(* temporary indentation *)
let  inlet  inlet  inlet  inlet  inlet  in in fmtBinder (pi,  , name,  , id,  , fmtType,  , fmtBody) no -> let let  in in sexp [str "<om:OMA>"; nl_ind (); str "<om:OMS cd=\"twelf\" name=\"arrow\"/>"; nl (); fmtExp (g,  , (v1,  , s),  , 0); nl (); fmtExp (g',  , (v2,  , dot1 s),  , 0); nl_unind (); str "</om:OMA>"]) fmtExpW(g,  , (root (h,  , s),  , s),  , _) let let  inlet  inlet  in in ! out fmtExpW(g,  , (lam (d,  , u),  , s),  , imp) let let  inlet  inlet  in(* temporary indentation *)
let  inlet  inlet  inlet  inlet  inlet  in in fmtBinder (lam,  , name,  , id,  , fmtType,  , fmtBody) fmtExpW(g,  , (fgnExp (csid,  , f),  , s),  , 0) sexp [str "FgnExp"](* FIX -cs Fri Jan 28 17:45:43 2005 *)
(* I.EClo, I.Redex, I.EVar not possible *)
 fmtExp(g,  , (u,  , s),  , imp) fmtExpW (g,  , whnf (u,  , s),  , imp)(* fmtSpine (G, (S, s), args) = fmts
     format spine S[s] at printing depth d, printing length l, in printing
     context G which approximates G', where G' |- S[s] is valid
     args is the number of arguments after which </om:OMA> must be inserted, no effect if negative
  *)
 fmtSpine(g,  , (nil,  , _),  , _) nl_unind () fmtSpine(g,  , (sClo (s,  , s'),  , s),  , args) fmtSpine (g,  , (s,  , comp (s',  , s)),  , args) fmtSpine(g,  , (app (u,  , s),  , s),  , args) let (* print first argument, 0 is dummy value *)
let  in(* close application if args reaches 0 *)
let  in(* print remaining arguments *)
 in ! out ^ fmtSpine (g,  , (s,  , s),  , args - 1) fmtExpTop(g,  , (u,  , s),  , imp) sexp [str "<om:OMOBJ>"; nl_ind (); fmtExp (g,  , (u,  , s),  , imp); nl_unind (); str "</om:OMOBJ>"](* top-level and shared OMDoc output, used in fmtConDec *)
 fmtBinder(binder,  , varname,  , varid,  , typ,  , body) "<om:OMBIND>" ^ nl_ind () ^ "<om:OMS cd=\"twelf\" name=\"" ^ binder ^ "\"/>" ^ nl () ^ "<om:OMBVAR><om:OMATTR>" ^ nl_ind () ^ (if (! namesafe) then ("<om:OMATP><om:OMS cd=\"omdoc\" name=\"notation\"/><om:OMFOREIGN encoding=\"application/omdoc+xml\">" ^ "<presentation for=\"#" ^ varid ^ "\"><use format=\"twelf\">" ^ varname ^ "</use></presentation>" ^ "</om:OMFOREIGN></om:OMATP>") else (* In the presentation information for variables can be omitted since it's their name anyway *)
"") ^ "<om:OMATP>" ^ nl () ^ "<om:OMS cd=\"twelf\" name=\"oftype\"/>" ^ nl () ^ typ ^ nl () ^ "</om:OMATP>" ^ nl () ^ "<om:OMV name=\"" ^ varid ^ "\"/>" ^ nl_unind () ^ "</om:OMATTR></om:OMBVAR>" ^ nl () ^ body ^ nl_unind () ^ "</om:OMBIND>" fmtSymbol(name,  , v,  , imp) "<symbol name=\"" ^ name ^ "\">" ^ nl_ind () ^ "<type system=\"twelf\">" ^ nl_ind () ^ fmtExpTop (null,  , (v,  , id),  , imp) ^ nl_unind () ^ "</type>" ^ nl_unind () ^ "</symbol>" fmtDefinition(name,  , u,  , imp) "<definition xml:id=\"" ^ name ^ ".def\" for=\"#" ^ name ^ "\">" ^ nl_ind () ^ fmtExpTop (null,  , (u,  , id),  , imp) ^ nl_unind () ^ "</definition>" fmtPresentation(cid) let let  inlet  inlet  inlet  inlet  inlet  inlet  inlet  inlet  inlet  inlet  in in presString1 ^ ">" ^ nl_ind () ^ useString1 ^ useString2 ^ nl_unind () ^ presString2 ^ nl () ^ presString1 ^ " role=\"applied\"" ^ fixString ^ precString ^ bracString ^ sepString ^ implicitString ^ ">" ^ nl_ind () ^ useString1 ^ useString2 ^ nl_unind () ^ presString2(* fixity string attached to omdoc file in private element (no escaping, fixity string cannot contain ]]>) *)
 fmtFixity(cid) let let  inlet  in in if (fixity = nonfix) then "" else nl () ^ "<private for=\"#" ^ (name cid) ^ "\">" ^ nl_ind () ^ "<data format=\"twelf\"><![CDATA[" ^ (toString fixity) ^ " " ^ name ^ ".]]></data>" ^ nl_unind () ^ "</private>"(* fmtConDec (condec) = fmt
     formats a constant declaration (which must be closed and in normal form)

     This function prints the quantifiers and abstractions only if hide = false.
  *)
let rec fmtConDec(cid,  , conDec (name,  , parent,  , imp,  , _,  , v,  , l)) let let  inlet  in in fmtSymbol (name,  , v,  , imp) fmtConDec(_,  , skoDec (name,  , parent,  , imp,  , v,  , l)) str ("<!-- Skipping Skolem constant " ^ name ^ "-->") fmtConDec(cid,  , conDef (name,  , parent,  , imp,  , u,  , v,  , l,  , _)) let let  inlet  in in fmtSymbol (name,  , v,  , imp) ^ nl () ^ fmtDefinition (name,  , u,  , imp) fmtConDec(cid,  , abbrevDef (name,  , parent,  , imp,  , u,  , v,  , l)) let let  inlet  in in fmtSymbol (name,  , v,  , imp) ^ nl () ^ fmtDefinition (name,  , u,  , imp) fmtConDec(_,  , blockDec (name,  , _,  , _,  , _)) str ("<!-- Skipping Skolem constant " ^ name ^ "-->")(* In the functions below, G must be a "printing context", that is,
     (a) unique names must be assigned to each declaration which may
         actually applied in the scope (typically, using Names.decName)
     (b) types need not be well-formed, since they are not used
  *)
let rec formatExp(g,  , u,  , imp) fmtExp (g,  , (u,  , id),  , imp)(*  fun formatSpine (G, S) = sexp (fmtSpine (G, (S, I.id))) *)
let rec formatConDec(condec) fmtConDec (condec)(* fun expToString (G, U) = F.makestring_fmt (formatExp (G, U, 0)) *)
let rec conDecToString(condec) (formatConDec (condec))let rec fmtConstcid formatConDec (cid,  , sgnLookup cid) ^ "\n" ^ fmtPresentation (cid) ^ fmtFixity (cid)let rec printConstcid (namesafe := false; fmtConst cid)let rec printSgnfilenamens let let  inlet  inlet  inlet  inlet  inlet  inlet  inlet  in in ()(* local ... *)
end