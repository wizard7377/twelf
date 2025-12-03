(* Termination Order *)
(* Author: Carsten Schuermann *)

module type ORDER =
sig

  (*! module IntSyn : INTSYN !*)

  exception Error of string

  type 'a Order =	       	        (* Orders                     *)
      Arg of 'a				(* O ::= x                    *)
    | Lex of 'a Order list              (*     | {O1 .. On}           *)
    | Simul of 'a Order list            (*     | [O1 .. On]           *)

  type Predicate =                  (* Reduction Order            *)
      Less of int Order * int Order     (* O < O'                     *)
    | Leq of int Order * int Order      (* O <= O'                    *)
    | Eq of int Order * int Order       (* O = O'                     *)

  type Mutual =			(* Termination ordering       *)
      Empty				(* O ::= No order specified   *)
    | LE of IntSyn.cid * Mutual		(*     | mutual dependencies  *)
    | LT of IntSyn.cid * Mutual		(*     | lex order for  -     *)

  type TDec =			(* Termination declaration *)
      TDec of int Order * Mutual

  type RDec =			(* Reduction declaration      *)
      RDec of Predicate * Mutual

  val reset : unit -> unit
  val resetROrder : unit -> unit

  val install : IntSyn.cid * TDec -> unit 
  val uninstall : IntSyn.cid -> bool
  val installROrder : IntSyn.cid * RDec -> unit 
  val uninstallROrder : IntSyn.cid -> bool

  val selLookup : IntSyn.cid -> int Order
  val selLookupROrder : IntSyn.cid -> Predicate
  
  val mutLookup : IntSyn.cid -> Mutual
  val closure : IntSyn.cid -> IntSyn.cid list

end;  (* module type ORDER *)
