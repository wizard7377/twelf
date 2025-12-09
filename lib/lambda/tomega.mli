(* Internal syntax for Delphin *)
(* Author: Carsten Schuermann *)

module type TOMEGA = 
sig
  (*! module IntSyn : INTSYN !*)

  (* make abstract *)
  type label = int      
  type lemma = int 

  type worlds = Worlds of IntSyn.cid list

  type quantifier = Implicit | Explicit


  type tC	=			(* Terminiation Condition     *)
    Abs of IntSyn.dec * tC      	(* T ::= {{D}} O              *)
  | Conj of tC * tC			(*     | O1 ^ O2              *)
  | Base of ((IntSyn.exp * IntSyn.Sub) * 
	     (IntSyn.exp * IntSyn.Sub)) Order.Order

  type for  			(* Formulas                   *)
  = World of worlds * for               (* F ::= World l1...ln. F     *)  
  | All of (Dec * quantifier) * for     (*     | All LD. F            *)
  | Ex  of (IntSyn.dec * quantifier)  * for
					(*     | Ex  D. F             *)
  | True				(*     | T                    *)
  | And of for * for                    (*     | F1 ^ F2              *)
  | FClo of for * Sub			(*     | F [t]                *)
  | FVar of (Dec IntSyn.ctx * For option ref)
					(*     | F (G)                *)

  and Dec =			        (* Declaration:               *)
    UDec of IntSyn.dec                  (* D ::= x:A                  *)
  | PDec of string option * For * TC option * TC option  
                                        (*     | xx :: F              *)

  and Prg =				(* Programs:                  *)
    Box of Worlds * Prg                 (*     | box W. P             *)
  | Lam of Dec * Prg	 	        (*     | lam LD. P            *)
  | New of Prg                          (*     | new P                *)
  | Choose of Prg                       (*     | choose P             *)
  | PairExp of IntSyn.exp * Prg         (*     | <M, P>               *)
  | PairBlock of IntSyn.Block * Prg     (*     | <rho, P>             *) 
  | PairPrg of Prg * Prg                (*     | <P1, P2>             *)
  | Unit				(*     | <>                   *)
  | Redex of Prg * Spine
  | Rec of Dec * Prg			(*     | mu xx. P             *)
  | Case of Cases                       (*     | case t of O          *)
  | PClo of Prg * Sub			(*     | P [t]                *)
  | Let of Dec * Prg * Prg              (*     | let D = P1 in P2     *)
  | EVar of Dec IntSyn.ctx * Prg option ref * For * TC option * TC option * IntSyn.exp
					(*     | E (G, F, _, _, X)    *)
                                        (* X is just just for printing*)
    
  | Const of lemma                      (* P ::= cc                   *)
  | Var of int                          (*     | xx                   *)
  | LetPairExp of IntSyn.dec * Dec * Prg * Prg
  | LetUnit of Prg * Prg

  and Spine =				(* Spines:                    *)
    Nil					(* S ::= Nil                  *)
  | AppExp of IntSyn.exp * Spine        (*     | P U                  *) 
  | AppBlock of IntSyn.Block * Spine    (*     | P rho                *)
  | AppPrg of Prg * Spine               (*     | P1 P2                *)
  | SClo of Spine * Sub                 (*     | S [t]                *) 
 
  and Sub =				(* Substitutions:             *)
    Shift of int			(* t ::= ^n                   *)
  | Dot of Front * Sub			(*     | F . t                *)
      
  and Front =				(* Fronts:                    *)
    Idx of int		  	        (* F ::= i                    *)
  | Prg of Prg				(*     | p                    *)
  | Exp of IntSyn.exp			(*     | U                    *)
  | Block of IntSyn.Block		(*     | _x                   *)
  | Undef                               (*     | _                    *)

  and Cases =				(* Cases                      *)
    Cases of (Dec IntSyn.ctx * Sub * Prg) list
					(* C ::= (Psi' |> s |-> P)    *)

  type conDec =			(* ConDec                     *)
    ForDec of string * For		(* CD ::= f :: F              *)
  | ValDec of string * Prg * For	(*      | f == P              *)

  exception NoMatch
  val coerceSub : Sub -> IntSyn.Sub
  val embedSub  : IntSyn.Sub -> Sub
  val coerceCtx : Dec IntSyn.ctx -> IntSyn.dec IntSyn.ctx
  val strengthenCtx : Dec IntSyn.ctx -> (IntSyn.dec IntSyn.ctx * Sub * Sub)
  val embedCtx  : IntSyn.dec IntSyn.ctx -> Dec IntSyn.ctx
  val weakenSub : Dec IntSyn.ctx -> Sub
  val invertSub : Sub -> Sub
  val id        : Sub
  val shift     : Sub
  val dot1      : Sub -> Sub
  val dotEta    : Front * Sub -> Sub
  val comp      : Sub * Sub -> Sub
  val varSub    : int * Sub -> Front
  val decSub    : Dec * Sub -> Dec
  val forSub    : For * Sub -> For
  val whnfFor   : For * Sub -> For * Sub
  val normalizePrg : Prg * Sub -> Prg 
  val normalizeSub : Sub -> Sub 
  val derefPrg : Prg -> Prg 
  
  val lemmaLookup : lemma -> ConDec
  val lemmaName   : string -> lemma
  val lemmaAdd    : ConDec -> lemma
  val lemmaSize   : unit -> int
  val lemmaDef    : lemma -> Prg
  val lemmaFor    : lemma -> For

  val eqWorlds    : Worlds * Worlds -> bool

  val convFor     : (For * Sub) * (For * Sub) -> bool
  val newEVar     : Dec IntSyn.ctx * For -> Prg
  val newEVarTC   : Dec IntSyn.ctx * For * TC option * TC option -> Prg 

(* Below are added by Yu Liao *)
  val ctxDec : Dec IntSyn.ctx * int -> Dec
  val revCoerceSub : IntSyn.Sub -> Sub
  val revCoerceCtx : IntSyn.dec IntSyn.ctx -> Dec IntSyn.ctx

(* Added references by ABP *)
  val coerceFront : Front -> IntSyn.Front
  val revCoerceFront : IntSyn.Front -> Front
  val deblockify : IntSyn.dec IntSyn.ctx -> IntSyn.dec IntSyn.ctx * Sub

(* Stuff that has to do with termination conditions *)
  val TCSub : TC * IntSyn.Sub -> TC
  val normalizeTC : TC -> TC
  val convTC : TC * TC -> bool
  val transformTC : IntSyn.dec IntSyn.ctx * For * int Order.Order list -> TC
    

end (* Signature TOMEGA *)




