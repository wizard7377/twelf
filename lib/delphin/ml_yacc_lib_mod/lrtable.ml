(* ML-Yacc Parser Generator (c) 1989 Andrew W. Appel, David R. Tarditi 
 *
 * $Log: not supported by cvs2svn $
 * Revision 1.1.2.1  2003/01/14 22:46:39  carsten_lf
 * delphin frontend added
 *
 * Revision 1.1  2001/11/12 23:23:09  carsten
 * mlyacc hack included
 *
 * Revision 1.1.1.1  1999/12/03 19:59:22  dbm
 * Import of 110.0.6 src
 *
 * Revision 1.1.1.1  1997/01/14 01:38:04  george
 *   Version 109.24
 *
 * Revision 1.1.1.1  1996/01/31  16:01:42  george
 * Version 109
 * 
 *)

module LrTable : LR_TABLE = 
    struct
	open Array List
	infix 9 sub
	type ('a,'b) pairlist = EMPTY
				  | PAIR of 'a * 'b * ('a,'b) pairlist
	type term = T of int
	type nonterm = NT of int
	type state = STATE of int
	type action = SHIFT of state
			| REDUCE of int (* rulenum from grammar *)
			| ACCEPT
			| ERROR
	exception Goto of state * nonterm
	type table = {states: int, rules : int,initialState: state,
		      action: ((term,action) pairlist * action) array,
		      goto :  (nonterm,state) pairlist array}
	let numStates = fn ({states,...} : table) => states
	let numRules = fn ({rules,...} : table) => rules
	let describeActions =
	   fn ({action,...} : table) => 
	           fn (STATE s) => action sub s
	let describeGoto =
	   fn ({goto,...} : table) =>
	           fn (STATE s) => goto sub s
	fun findTerm (T term,row,default) =
	    let fun find (PAIR (T key,data,r)) =
		       if key < term then find r
		       else if key=term then data
		       else default
		   | find EMPTY = default
	    in find row
	    end
	fun findNonterm (NT nt,row) =
	    let fun find (PAIR (NT key,data,r)) =
		       if key < nt then find r
		       else if key=nt then SOME data
		       else NONE
		   | find EMPTY = NONE
	    in find row
	    end
	let action = fn ({action,...} : table) =>
		fn (STATE state,term) =>
		  let let (row,default) = action sub state
		  in findTerm(term,row,default)
		  end
	let goto = fn ({goto,...} : table) =>
			fn (a as (STATE state,nonterm)) =>
			  case findNonterm(nonterm,goto sub state)
			  of SOME state => state
			   | NONE => raise (Goto a)
	let initialState = fn ({initialState,...} : table) => initialState
	let mkLrTable = fn {actions,gotos,initialState,numStates,numRules} =>
	     ({action=actions,goto=gotos,
	       states=numStates,
	       rules=numRules,
               initialState=initialState} : table)
end;
