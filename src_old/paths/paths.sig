(* Paths, Occurrences, and Error Locations *)
(* Author: Frank Pfenning *)

signature PATHS =
sig

  datatype region = Reg of int * int	(* r ::= (i,j) is interval [i,j) *)
  datatype location = Loc of string * region (* loc ::= (filename, region) *)

  (* line numbering, used when printing regions *)
  type lines_info			(* mapping from character positions to lines in a file *)
  val resetLines : unit -> unit         (* reset line numbering *)
  val newLine : int -> unit		(* new line starts at character i *)
  val getLinesInfo : unit -> lines_info  (* get lines info for current file *)

  val join : region * region -> region	(* join(r1,r2) = smallest region enclosing r1 and r2 *)
  val toString : region -> string	(* line1.col1-line2.col2, parsable by Emacs *)
  val wrap : region * string -> string  (* add region to error message, parsable by Emacs *)
  val wrapLoc : location * string -> string  (* add location to error message, also parsable *)
  val wrapLoc' : location * lines_info option * string -> string
					(* add location to error message in line.col format *)

  (* Paths, occurrences and occurrence trees only work well for normal forms *)
  (* In the general case, regions only approximate true source location *)

  (* Follow path through a term to obtain subterm *)
  datatype path =
     Label of path			(* [x:#] U or {x:#} V *)
   | Body of path			(* [x:V] # or {x:V} # *)
   | Head				(* # @ S, term in normal form *)
   | Arg of int * path			(* H @ S1; ...; #; ...; Sn; Nil *)
   | Here				(* #, covers Uni, EVar, Redex(?) *)

  (*
     Construct an occurrence when traversing a term.
     The resulting occurrence can be translated to a region
     via an occurrence tree stored with the term.

     An occurrence is a path in reverse order.
  *)
  type occ
  val top : occ
  val label : occ -> occ
  val body : occ -> occ
  val head : occ -> occ
  val arg : int * occ -> occ

  (*
     An occurrence tree is a data structure mapping occurrences in a term
     to regions in an input stream.  Occurrence trees are constructed during parsing.
  *)
  type occ_exp				(* occurrence tree for u expressions *)
  and occ_spine				(* occurrence tree for s spines *)

  val leaf : region -> occ_exp		(* could be _ or identifier *)
  val bind : region * occ_exp option * occ_exp -> occ_exp
  val root : region * occ_exp * int * int * occ_spine -> occ_exp
  val app : occ_exp * occ_spine -> occ_spine
  val nils : occ_spine

  type occ_con_dec			(* occurrence tree for constant declarations *)
  val dec : int * occ_exp -> occ_con_dec   (* (#implicit, v) in c : V *)
  val def : int * occ_exp * occ_exp option -> occ_con_dec
					(* (#implicit, u, v) in c : V = U *)

  val toRegion : occ_exp -> region
  val toRegionSpine : occ_spine * region -> region

  val posToPath : occ_exp -> int -> path

  val occToRegionExp : occ_exp -> occ -> region
  val occToRegionDec : occ_con_dec -> occ -> region (* into v for c : V *)
  val occToRegionDef1 : occ_con_dec -> occ -> region (* into u for c : V = U *)
  val occToRegionDef2 : occ_con_dec -> occ -> region (* into v for c : V = U *)
  val occToRegionClause : occ_con_dec -> occ -> region (* into v for c : V ... *)

end;  (* signature PATHS *)
