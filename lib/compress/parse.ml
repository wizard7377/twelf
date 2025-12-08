module Parse = 
struct

  open Parsing
  open Tok
  (* infixr 4 << >> *)
  (* infixr 3 && *)
  (* infix  2 -- ## *)
  (* infix  2 wth suchthat return guard when *)
  (* infixr 1 || *)
  let backtick = literal

  type mode = MMINUS
		| MPLUS
		| MOMIT

  type term = Id of string
		| App of term * term
		| Lam of (string * term option) * term
		| Type
		| Pi of mode * (string * term option) * term
		| Arrow of term * term
		| PlusArrow of term * term
		| Ascribe of term * term
		| Omit

  let PiMinus ((s, to_), t) = Pi (MMINUS, (s, to_), t)
  let PiPlus ((s, to_), t) = Pi (MPLUS, (s, to_), t)
  let PiOmit ((s, to_), t) = Pi (MOMIT, (s, to_), t)

  let rec modeToString = function
      MMINUS -> ""
    | MPLUS -> "+ "
    | MOMIT -> "* "

  let rec termToString = function
      (Id s) -> s
    | (App (t, u)) -> "(" ^ (termToString t) ^ " " ^ (termToString u) ^ ")"
    | (Lam (vd, t)) -> "[" ^ (vardecToString vd) ^ "] " ^ (termToString t)
    | (Pi (m, vd, t)) -> "{" ^ (modeToString m) ^ (vardecToString vd) ^ "} " ^ (termToString t)
    | (Type) -> "type"
    | (Arrow (t, u)) -> "(" ^ (termToString t) ^ " -> " ^ (termToString u) ^ ")"
    | (PlusArrow (t, u)) -> "(" ^ (termToString t) ^ " +> " ^ (termToString u) ^ ")"
    | (Ascribe (t, u)) -> "(" ^ (termToString t) ^ " : " ^ (termToString u) ^ ")"
    | (Omit) -> "*"
  and vardecToString = function
      (v, SOME t) -> v ^ ":" ^ (termToString t)
    | (v, NONE) -> v

  let id = maybe (function (ID s) -> SOME s | _ -> NONE)

  let swap(x,y) = (y,x)

  let rec vardec() = id << backtick COLON && ($term wth SOME) ||
		 id wth (fun s -> (s, NONE)) 
  and term() = parsefixityadj (
	       alt[id wth (Atm o Id),
		   backtick LPAREN >> $term << backtick RPAREN wth Atm,
		   backtick LPAREN >> $term << backtick COLON &&
			   $term << backtick RPAREN wth (Atm o Ascribe),
		   backtick LBRACKET >> $vardec << backtick RBRACKET && $term wth (Atm o Lam),
		   backtick LBRACE >> backtick STAR >> $vardec << backtick RBRACE && $term wth (Atm o PiOmit),
		   backtick LBRACE >> backtick PLUS >> $vardec << backtick RBRACE && $term wth (Atm o PiPlus),
		   backtick LBRACE >> $vardec << backtick RBRACE && $term wth (Atm o PiMinus),
		   backtick TYPE return (Atm Type),
		   backtick ARROW return Opr(Infix(Right, 5, Arrow)),
		   backtick PLUSARROW return Opr(Infix(Right, 5, PlusArrow)),
		   backtick BACKARROW return Opr(Infix(Left, 5, Arrow o swap)),
		   backtick STAR return (Atm Omit)
		  ]) Left App
		   
  let condec = (opt (backtick MINUS) wth (not o Option.isSome)) && id << backtick COLON && $term << backtick DOT


  let parseof x =  Stream.toList (Parsing.transform ($term)
				 (Parsing.transform (!!tok)
				  (Pos.markstream (StreamUtil.stostream (x ^ "\n%.")))))
end
