(* Termination Order *)
(* Author: Carsten Schuermann *)

signature ORDER =
sig

  (*! structure IntSyn : INTSYN !*)

  exception Error of string

  datatype 'a order =	       	        (* Orders                     *)
      Arg of 'a				(* O ::= x                    *)
    | Lex of 'a order list              (*     | {O1 .. On}           *)
    | Simul of 'a order list            (*     | [O1 .. On]           *)

  datatype predicate =                  (* Reduction Order            *)
      Less of int order * int order     (* O < O'                     *)
    | Leq of int order * int order      (* O <= O'                    *)
    | Eq of int order * int order       (* O = O'                     *)

  datatype mutual =			(* Termination ordering       *)
      Empty				(* O ::= No order specified   *)
    | LE of IntSyn.cid * mutual		(*     | mutual dependencies  *)
    | LT of IntSyn.cid * mutual		(*     | lex order for  -     *)

  datatype t_dec =			(* Termination declaration *)
      TDec of int order * mutual

  datatype r_dec =			(* Reduction declaration      *)
      RDec of predicate * mutual

  val reset : unit -> unit
  val resetROrder : unit -> unit

  val install : IntSyn.cid * t_dec -> unit 
  val uninstall : IntSyn.cid -> bool
  val installROrder : IntSyn.cid * r_dec -> unit 
  val uninstallROrder : IntSyn.cid -> bool

  val selLookup : IntSyn.cid -> int order
  val selLookupROrder : IntSyn.cid -> predicate
  
  val mutLookup : IntSyn.cid -> mutual
  val closure : IntSyn.cid -> IntSyn.cid list

end;  (* signature ORDER *)
