structure Parse = 
struct

  open Parsing
  open Tok
  infixr 4 << >>
  infixr 3 &&
  infix  2 -- ##
  infix  2 wth suchthat return guard when
  infixr 1 ||
  val ` = literal

  datatype mode = MMINUS
		| MPLUS
		| MOMIT

  datatype term = Id of string
		| App of term * term
		| Lam of (string * term option) * term
		| Type
		| Pi of mode * (string * term option) * term
		| Arrow of term * term
		| PlusArrow of term * term
		| Ascribe of term * term
		| Omit

  fun piMinus ((s, to), t) = Pi (MMINUS, (s, to), t)
  fun piPlus ((s, to), t) = Pi (MPLUS, (s, to), t)
  fun piOmit ((s, to), t) = Pi (MOMIT, (s, to), t)

  fun modeToString MMINUS = ""
    | modeToString MPLUS = "+ "
    | modeToString MOMIT = "* "

  fun termToString (Id s) = s
    | termToString (App (t, u)) = "(" ^ (termToString t) ^ " " ^ (termToString u) ^ ")"
    | termToString (Lam (vd, t)) = "[" ^ (vardecToString vd) ^ "] " ^ (termToString t)
    | termToString (Pi (m, vd, t)) = "{" ^ (modeToString m) ^ (vardecToString vd) ^ "} " ^ (termToString t)
    | termToString (Type) = "type"
    | termToString (Arrow (t, u)) = "(" ^ (termToString t) ^ " -> " ^ (termToString u) ^ ")"
    | termToString (PlusArrow (t, u)) = "(" ^ (termToString t) ^ " +> " ^ (termToString u) ^ ")"
    | termToString (Ascribe (t, u)) = "(" ^ (termToString t) ^ " : " ^ (termToString u) ^ ")"
    | termToString (Omit) = "*"
  and vardecToString (v, SOME t) = v ^ ":" ^ (termToString t)
    | vardecToString (v, NONE) = v

  val id = maybe (fn (ID s) => SOME s | _ => NONE)

  fun swap(x,y) = (y,x)

  fun vardec() = id << `COLON && ($term wth SOME) ||
		 id wth (fn s => (s, NONE)) 
  and term() = parsefixityadj (
	       alt[id wth (Atm o Id),
		   `LPAREN >> $term << `RPAREN wth Atm,
		   `LPAREN >> $term << `COLON &&
			   $term << `RPAREN wth (Atm o Ascribe),
		   `LBRACKET >> $vardec << `RBRACKET && $term wth (Atm o Lam),
		   `LBRACE >> `STAR >> $vardec << `RBRACE && $term wth (Atm o piOmit),
		   `LBRACE >> `PLUS >> $vardec << `RBRACE && $term wth (Atm o piPlus),
		   `LBRACE >> $vardec << `RBRACE && $term wth (Atm o piMinus),
		   `TYPE return (Atm Type),
		   `ARROW return Opr(Infix(Right, 5, Arrow)),
		   `PLUSARROW return Opr(Infix(Right, 5, PlusArrow)),
		   `BACKARROW return Opr(Infix(Left, 5, Arrow o swap)),
		   `STAR return (Atm Omit)
		  ]) Left App
		   
  val condec = (opt (`MINUS) wth (not o Option.isSome)) && id << `COLON && $term << `DOT


  fun parseof x =  Stream.toList (Parsing.transform ($term)
				 (Parsing.transform (!!tok)
				  (Pos.markstream (StreamUtil.stostream (x ^ "\n%.")))))
end
