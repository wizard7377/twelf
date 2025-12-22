(* Meta syntax *)

(* Author: Carsten Schuermann *)

module type METASYN = sig
  (*! structure IntSyn : INTSYN !*)
  type mode = Bot | Top

  (*     | Top                  *)
  type prefix =
    | Prefix of
        IntSyn.dctx (* G   declarations           *)
        * mode IntSyn.ctx (* Mtx modes                  *)
        * int IntSyn.ctx

  (* Btx splitting depths       *)
  type state =
    | State of
        string (*             [name]         *)
        * prefix (*             G; Mtx; Btx    *)
        * IntSyn.exp

  (*             |- V           *)
  type sgn = SgnEmpty | ConDec of IntSyn.conDec * sgn

  (*      | c:V, IS             *)
  val createAtomConst : IntSyn.dctx * IntSyn.head -> IntSyn.exp * IntSyn.eclo
  val createAtomBVar : IntSyn.dctx * int -> IntSyn.exp * IntSyn.eclo
end

(* signature METASYN *)
