module Parse = 
struct

  open Parsing
  open Tok
  infixr 4 << >>
  infixr 3 &&
  infix  2 -- ##
  infix  2 wth suchthat return guard when
  infixr 1 ||
  let ` = literal

  type mode = mMINUS
		| mPLUS
		| mOMIT

  type term = Id of string
		| App of term * term
		| Lam of (string * term option) * term
		| Type
		| Pi of mode * (string * term option) * term
		| Arrow of term * term
		| PlusArrow of term * term
		| Ascribe of term * term
		| Omit

  let rec PiMinus ((s, to), t) = Pi (mMINUS, (s, to), t)
  let rec PiPlus ((s, to), t) = Pi (mPLUS, (s, to), t)
  let rec PiOmit ((s, to), t) = Pi (mOMIT, (s, to), t)

  let rec modeToString = function mMINUS -> ""
    | mPLUS -> "+ "
    | mOMIT -> "* "

  let rec termToString = function (Id s) -> s
    | (App (t, u)) -> "(" ^ (termToString t) ^ " " ^ (termToString u) ^ ")"
    | (Lam (vd, t)) -> "[" ^ (vardecToString vd) ^ "] " ^ (termToString t)
    | (Pi (m, vd, t)) -> "{" ^ (modeToString m) ^ (vardecToString vd) ^ "} " ^ (termToString t)
    | (Type) -> "type"
    | (Arrow (t, u)) -> "(" ^ (termToString t) ^ " -> " ^ (termToString u) ^ ")"
    | (PlusArrow (t, u)) -> "(" ^ (termToString t) ^ " +> " ^ (termToString u) ^ ")"
    | (Ascribe (t, u)) -> "(" ^ (termToString t) ^ " : " ^ (termToString u) ^ ")"
    | (Omit) -> "*"
  and vardecToString (v, SOME t) = v ^ ":" ^ (termToString t)
    | vardecToString (v, NONE) = v

  let id = maybe (fn (ID s) => SOME s | _ => NONE)

  let rec swap(x,y) = (y,x)

  let rec vardec() = id << `COLON && ($term wth SOME) ||
		 id wth (fun s -> (s, NONE)) 
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
		   
  let condec = (opt (`MINUS) wth (not o Option.isSome)) && id << `COLON && $term << `DOT


  let rec parseof x =  Stream.toList (Parsing.transform ($term)
				 (Parsing.transform (!!tok)
				  (Pos.markstream (StreamUtil.stostream (x ^ "\n%.")))))
end
