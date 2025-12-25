open Basis ;; 

module Parse = struct
  open Parsing
  open Tok

  let tick = literal

  type mode = MMinus | MPlus | MOmit

  type term =
    | Id of string
    | App of term * term
    | Lam of (string * term option) * term
    | Type
    | Pi of mode * (string * term option) * term
    | Arrow of term * term
    | PlusArrow of term * term
    | Ascribe of term * term
    | Omit

  let rec piMinus ((s, to_), t) = Pi (MMinus, (s, to_), t)
  let rec piPlus ((s, to_), t) = Pi (MPlus, (s, to_), t)
  let rec piOmit ((s, to_), t) = Pi (MOmit, (s, to_), t)
  let rec modeToString = function MMinus -> "" | MPlus -> "+ " | MOmit -> "* "

  let rec termToString = function
    | Id s -> s
    | App (t, u) -> "(" ^ termToString t ^ " " ^ termToString u ^ ")"
    | Lam (vd, t) -> "[" ^ vardecToString vd ^ "] " ^ termToString t
    | Pi (m, vd, t) ->
        "{" ^ modeToString m ^ vardecToString vd ^ "} " ^ termToString t
    | Type -> "type"
    | Arrow (t, u) -> "(" ^ termToString t ^ " -> " ^ termToString u ^ ")"
    | PlusArrow (t, u) -> "(" ^ termToString t ^ " +> " ^ termToString u ^ ")"
    | Ascribe (t, u) -> "(" ^ termToString t ^ " : " ^ termToString u ^ ")"
    | Omit -> "*"

  and vardecToString = function
    | v, Some t -> v ^ ":" ^ termToString t
    | v, None -> v

  let id = maybe (function ID s -> Some s | _ -> None)
  let rec swap (x, y) = (y, x)

  let rec vardec () =
    (id << tick COLON && wth (( $ ) term) Some) || wth id (fun s -> (s, None))

  and term () = assert false (* TODO: Fix this file (SEE ATTACHED) *)

  (* and term ()  =
	parsefixityadj
		(alt
			 [ wth id (Atm o Id);
				 wth (tick LPAREN >> ( $ ) term << tick RPAREN) Atm;
				 wth (tick LPAREN >> ( $ ) term << tick COLON && ( $ ) term << tick RPAREN) (Atm o Ascribe);
				 wth (tick LBRACKET >> ( $ ) vardec << tick RBRACKET && ( $ ) term) (Atm o Lam);
				 wth (tick LBRACE >> tick STAR >> ( $ ) vardec << tick RBRACE && ( $ ) term) (Atm o piOmit);
				 wth (tick LBRACE >> tick PLUS >> ( $ ) vardec << tick RBRACE && ( $ ) term) (Atm o piPlus);
				 wth (tick LBRACE >> ( $ ) vardec << tick RBRACE && ( $ ) term) (Atm o piMinus);
				 tick TYPE return (Atm Type);
				 tick ARROW return Opr (Infix (Right, 5, Arrow));
				 tick PLUSARROW return Opr (Infix (Right, 5, PlusArrow));
				 tick BACKARROW return Opr (Infix (Left, 5, Arrow o swap));
				 tick STAR return (Atm Omit)
			 ])
		Left App *)
  (*
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
			 *)
  let condec =
    wth (opt (tick MINUS)) (not o Option.isSome)
    && id << tick COLON
    && ( $ ) term << tick DOT

  let rec parseof x =
    Stream.toList
      (Parsing.transform (( $ ) term)
         (Parsing.transform !!tok
            (Pos.markstream (StreamUtil.stostream (x ^ "\n%.")))))
end
