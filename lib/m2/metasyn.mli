(* Meta syntax *)
(* Author: Carsten Schuermann *)

module type METASYN =
sig
  (*! module IntSyn : INTSYN !*)

  type Mode =			(* Mode                       *)
    Bot					(* M ::= Bot                  *)
  | Top					(*     | Top                  *)

  type Prefix =			(* Prefix P := *)
    Prefix of IntSyn.dctx		(* G   declarations           *)
            * Mode IntSyn.Ctx		(* Mtx modes                  *)
            * int IntSyn.Ctx		(* Btx splitting depths       *)

  type State =			(* State S :=                 *)
    State of string			(*             [name]         *)
             * Prefix			(*             G; Mtx; Btx    *)
             * IntSyn.Exp		(*             |- V           *)

  type Sgn =			(* Interface module type        *)
    SgnEmpty				(* IS ::= .                   *)
  | ConDec of IntSyn.ConDec * Sgn       (*      | c:V, IS             *)

  val createAtomConst : IntSyn.dctx * IntSyn.Head -> (IntSyn.Exp * IntSyn.eclo)
  val createAtomBVar : IntSyn.dctx * int -> (IntSyn.Exp * IntSyn.eclo)
end; (* module type METASYN *)
