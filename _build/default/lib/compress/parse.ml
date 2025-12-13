structure Parse = 
struct

  open Parsing
  open Tok
  infixr 4 << >>
  infixr 3 &&
  infix  2 -- ##
  infix  2 wth suchthat return guard when
  infixr 1 ||
  (* GEN BEGIN TAG OUTSIDE LET *) val ` = literal (* GEN END TAG OUTSIDE LET *)

  datatype mode = mMINUS
		| mPLUS
		| mOMIT

  datatype term = Id of string
		| App of term * term
		| Lam of (string * term option) * term
		| Type
		| Pi of mode * (string * term option) * term
		| Arrow of term * term
		| PlusArrow of term * term
		| Ascribe of term * term
		| Omit

  fun PiMinus ((s, to), t) = Pi (mMINUS, (s, to), t)
  fun PiPlus ((s, to), t) = Pi (mPLUS, (s, to), t)
  fun PiOmit ((s, to), t) = Pi (mOMIT, (s, to), t)

  fun (* GEN BEGIN CASE FIRST *) (* GEN BEGIN CASE FIRST *) modeToString mMINUS = "" (* GEN END CASE FIRST *) (* GEN END CASE FIRST *)
    | (* GEN BEGIN CASE BRANCH *) modeToString mPLUS = "+ " (* GEN END CASE BRANCH *)
    | (* GEN BEGIN CASE BRANCH *) (* GEN BEGIN CASE BRANCH *) modeToString mOMIT = "* " (* GEN END CASE BRANCH *) (* GEN END CASE BRANCH *)

  fun (* GEN BEGIN CASE FIRST *) (* GEN BEGIN CASE FIRST *) termToString (Id s) = s (* GEN END CASE FIRST *) (* GEN END CASE FIRST *)
    | (* GEN BEGIN CASE BRANCH *) termToString (App (t, u)) = "(" ^ (termToString t) ^ " " ^ (termToString u) ^ ")" (* GEN END CASE BRANCH *)
    | (* GEN BEGIN CASE BRANCH *) termToString (Lam (vd, t)) = "[" ^ (vardecToString vd) ^ "] " ^ (termToString t) (* GEN END CASE BRANCH *)
    | (* GEN BEGIN CASE BRANCH *) termToString (Pi (m, vd, t)) = "{" ^ (modeToString m) ^ (vardecToString vd) ^ "} " ^ (termToString t) (* GEN END CASE BRANCH *)
    | (* GEN BEGIN CASE BRANCH *) termToString (Type) = "type" (* GEN END CASE BRANCH *)
    | (* GEN BEGIN CASE BRANCH *) termToString (Arrow (t, u)) = "(" ^ (termToString t) ^ " -> " ^ (termToString u) ^ ")" (* GEN END CASE BRANCH *)
    | (* GEN BEGIN CASE BRANCH *) termToString (PlusArrow (t, u)) = "(" ^ (termToString t) ^ " +> " ^ (termToString u) ^ ")" (* GEN END CASE BRANCH *)
    | (* GEN BEGIN CASE BRANCH *) termToString (Ascribe (t, u)) = "(" ^ (termToString t) ^ " : " ^ (termToString u) ^ ")" (* GEN END CASE BRANCH *)
    | (* GEN BEGIN CASE BRANCH *) (* GEN BEGIN CASE BRANCH *) termToString (Omit) = "*" (* GEN END CASE BRANCH *) (* GEN END CASE BRANCH *)
  and (* GEN BEGIN CASE FIRST *) (* GEN BEGIN CASE FIRST *) vardecToString (v, SOME t) = v ^ ":" ^ (termToString t) (* GEN END CASE FIRST *) (* GEN END CASE FIRST *)
    | (* GEN BEGIN CASE BRANCH *) (* GEN BEGIN CASE BRANCH *) vardecToString (v, NONE) = v (* GEN END CASE BRANCH *) (* GEN END CASE BRANCH *)

  (* GEN BEGIN TAG OUTSIDE LET *) val id = maybe ((* GEN BEGIN FUNCTION EXPRESSION *) fn (ID s) => SOME s | _ => NONE (* GEN END FUNCTION EXPRESSION *)) (* GEN END TAG OUTSIDE LET *)

  fun swap(x,y) = (y,x)

  fun vardec() = id << `COLON && ($term wth SOME) ||
  		 id wth ((* GEN BEGIN FUNCTION EXPRESSION *) (* GEN BEGIN FUNCTION EXPRESSION *) fn s => (s, NONE) (* GEN END FUNCTION EXPRESSION *) (* GEN END FUNCTION EXPRESSION *)) 
  and term() = parsefixityadj (
  	       alt[id wth (Atm o Id),
  		   `LPAREN >> $term << `RPAREN wth Atm,
  		   `LPAREN >> $term << `COLON &&
  			   $term << `RPAREN wth (Atm o Ascribe),
  		   `LBRACKET >> $vardec << `RBRACKET && $term wth (Atm o Lam),
  		   `LBRACE >> `STAR >> $vardec << `RBRACE && $term wth (Atm o PiOmit),
  		   `LBRACE >> `PLUS >> $vardec << `RBRACE && $term wth (Atm o PiPlus),
  		   `LBRACE >> $vardec << `RBRACE && $term wth (Atm o PiMinus),
  		   `TYPE return (Atm Type),
  		   `ARROW return Opr(Infix(Right, 5, Arrow)),
  		   `PLUSARROW return Opr(Infix(Right, 5, PlusArrow)),
  		   `BACKARROW return Opr(Infix(Left, 5, Arrow o swap)),
  		   `STAR return (Atm Omit)
  		  ]) Left App
		   
  (* GEN BEGIN TAG OUTSIDE LET *) val condec = (opt (`MINUS) wth (not o Option.isSome)) && id << `COLON && $term << `DOT (* GEN END TAG OUTSIDE LET *)


  fun parseof x =  Stream.toList (Parsing.transform ($term)
  				 (Parsing.transform (!!tok)
  				  (Pos.markstream (StreamUtil.stostream (x ^ "\n%.")))))
end
