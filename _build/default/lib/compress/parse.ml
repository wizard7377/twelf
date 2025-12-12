structure Parse = 
struct

  open Parsing
  open Tok
  infixr 4 << >>
  infixr 3 &&
  infix  2 -- ##
  infix  2 wth suchthat return guard when
  infixr 1 ||
  (* GEN BEGIN TAG INSIDE LET *) val ` = literal (* GEN END TAG INSIDE LET *)

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

  (* GEN BEGIN TAG INSIDE LET *) fun PiMinus ((s, to), t) = Pi (mMINUS, (s, to), t) (* GEN END TAG INSIDE LET *)
  (* GEN BEGIN TAG INSIDE LET *) fun PiPlus ((s, to), t) = Pi (mPLUS, (s, to), t) (* GEN END TAG INSIDE LET *)
  (* GEN BEGIN TAG INSIDE LET *) fun PiOmit ((s, to), t) = Pi (mOMIT, (s, to), t) (* GEN END TAG INSIDE LET *)

  (* GEN BEGIN TAG INSIDE LET *) fun modeToString mMINUS = ""
    | modeToString mPLUS = "+ "
    | modeToString mOMIT = "* " (* GEN END TAG INSIDE LET *)

  (* GEN BEGIN TAG INSIDE LET *) fun termToString (Id s) = s
    | termToString (App (t, u)) = "(" ^ (termToString t) ^ " " ^ (termToString u) ^ ")"
    | termToString (Lam (vd, t)) = "[" ^ (vardecToString vd) ^ "] " ^ (termToString t)
    | termToString (Pi (m, vd, t)) = "{" ^ (modeToString m) ^ (vardecToString vd) ^ "} " ^ (termToString t)
    | termToString (Type) = "type"
    | termToString (Arrow (t, u)) = "(" ^ (termToString t) ^ " -> " ^ (termToString u) ^ ")"
    | termToString (PlusArrow (t, u)) = "(" ^ (termToString t) ^ " +> " ^ (termToString u) ^ ")"
    | termToString (Ascribe (t, u)) = "(" ^ (termToString t) ^ " : " ^ (termToString u) ^ ")"
    | termToString (Omit) = "*"
  and vardecToString (v, SOME t) = v ^ ":" ^ (termToString t)
    | vardecToString (v, NONE) = v (* GEN END TAG INSIDE LET *)

  (* GEN BEGIN TAG INSIDE LET *) val id = maybe (fn (ID s) => SOME s | _ => NONE) (* GEN END TAG INSIDE LET *)

  (* GEN BEGIN TAG INSIDE LET *) fun swap(x,y) = (y,x) (* GEN END TAG INSIDE LET *)

  (* GEN BEGIN TAG INSIDE LET *) fun vardec() = id << `COLON && ($term wth SOME) ||
  		 id wth (fn s => (s, NONE)) 
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
  		  ]) Left App (* GEN END TAG INSIDE LET *)
		   
  (* GEN BEGIN TAG INSIDE LET *) val condec = (opt (`MINUS) wth (not o Option.isSome)) && id << `COLON && $term << `DOT (* GEN END TAG INSIDE LET *)


  (* GEN BEGIN TAG INSIDE LET *) fun parseof x =  Stream.toList (Parsing.transform ($term)
  				 (Parsing.transform (!!tok)
  				  (Pos.markstream (StreamUtil.stostream (x ^ "\n%."))))) (* GEN END TAG INSIDE LET *)
end
