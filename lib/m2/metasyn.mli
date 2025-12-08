(* Meta syntax *)
(* Author: Carsten Schuermann *)

module type METASYN =
sig
  (*! module IntSyn : INTSYN !*)

  type mode =			(* Mode                       *)
    Bot					(* M ::= Bot                  *)
  | Top					(*     | Top                  *)

  type prefix =			(* Prefix P := *)
    Prefix of IntSyn.dctx		(* G   declarations           *)
            * Mode IntSyn.ctx		(* Mtx modes                  *)
            * int IntSyn.ctx		(* Btx splitting depths       *)

  type state =			(* State S :=                 *)
    State of string			(*             [name]         *)
             * Prefix			(*             G; Mtx; Btx    *)
             * IntSyn.exp		(*             |- V           *)

  type Sgn =			(* Interface module type        *)
    SgnEmpty				(* IS ::= .                   *)
  | ConDec of IntSyn.ConDec * Sgn       (*      | c:V, IS             *)

  val createAtomConst : IntSyn.dctx * IntSyn.Head -> (IntSyn.exp * IntSyn.eclo)
  val createAtomBVar : IntSyn.dctx * int -> (IntSyn.exp * IntSyn.eclo)
end;; (* module type METASYN *)
