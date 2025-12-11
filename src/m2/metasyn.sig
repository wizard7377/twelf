(* Meta syntax *)
(* Author: Carsten Schuermann *)

signature METASYN =
sig
  (*! structure IntSyn : INTSYN !*)

  datatype mode =			(* Mode                       *)
    Bot					(* M ::= Bot                  *)
  | Top					(*     | Top                  *)

  datatype prefix =			(* Prefix P := *)
    Prefix of IntSyn.dctx		(* G   declarations           *)
            * mode IntSyn.ctx		(* Mtx modes                  *)
            * int IntSyn.ctx		(* Btx splitting depths       *)

  datatype state =			(* State S :=                 *)
    State of string			(*             [name]         *)
             * prefix			(*             G; Mtx; Btx    *)
             * IntSyn.exp		(*             |- V           *)

  datatype sgn =			(* Interface signature        *)
    SgnEmpty				(* IS ::= .                   *)
  | ConDec of IntSyn.con_dec * sgn       (*      | c:V, IS             *)

  val createAtomConst : IntSyn.dctx * IntSyn.head -> (IntSyn.exp * IntSyn.eclo)
  val createAtomBVar : IntSyn.dctx * int -> (IntSyn.exp * IntSyn.eclo)
end; (* signature METASYN *)
