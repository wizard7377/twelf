(* Internal syntax for Delphin *)
(* Author: Carsten Schuermann *)

(* GEN BEGIN SIGNATURE DECLARATION *) signature TOMEGA = 
sig
  (*! structure IntSyn : INTSYN !*)

  (* make abstract *)
  type label = int      
  type lemma = int 

  datatype worlds = Worlds of IntSyn.cid list
    
  datatype quantifier = Implicit | Explicit


  datatype tc	=			(* Terminiation Condition     *)
    Abs of IntSyn.dec * tc      	(* T ::= {{D}} O              *)
  | Conj of tc * tc			(*     | O1 ^ O2              *)
  | Base of ((IntSyn.exp * IntSyn.sub) * 
	     (IntSyn.exp * IntSyn.sub)) Order.order

  datatype for  			(* Formulas                   *)
  = World of worlds * for               (* F ::= World l1...ln. F     *)  
  | All of (dec * quantifier) * for     (*     | All LD. F            *)
  | Ex  of (IntSyn.dec * quantifier)  * for
					(*     | Ex  D. F             *)
  | True				(*     | T                    *)
  | And of for * for                    (*     | F1 ^ F2              *)
  | FClo of for * sub			(*     | F [t]                *)
  | FVar of (dec IntSyn.ctx * for option ref)
					(*     | F (G)                *)

  and dec =			        (* Declaration:               *)
    UDec of IntSyn.dec                  (* D ::= x:A                  *)
  | PDec of string option * for * tc option * tc option  
                                        (*     | xx :: F              *)

  and prg =				(* Programs:                  *)
    Box of worlds * prg                 (*     | box W. P             *)
  | Lam of dec * prg	 	        (*     | lam LD. P            *)
  | New of prg                          (*     | new P                *)
  | Choose of prg                       (*     | choose P             *)
  | PairExp of IntSyn.exp * prg         (*     | <M, P>               *)
  | PairBlock of IntSyn.block * prg     (*     | <rho, P>             *) 
  | PairPrg of prg * prg                (*     | <P1, P2>             *)
  | Unit				(*     | <>                   *)
  | Redex of prg * spine
  | Rec of dec * prg			(*     | mu xx. P             *)
  | Case of cases                       (*     | case t of O          *)
  | PClo of prg * sub			(*     | P [t]                *)
  | Let of dec * prg * prg              (*     | let D = P1 in P2     *)
  | EVar of dec IntSyn.ctx * prg option ref * for * tc option * tc option * IntSyn.exp
					(*     | E (G, F, _, _, X)    *)
                                        (* X is just just for printing*)
    
  | Const of lemma                      (* P ::= cc                   *)
  | Var of int                          (*     | xx                   *)
  | LetPairExp of IntSyn.dec * dec * prg * prg
  | LetUnit of prg * prg

  and spine =				(* Spines:                    *)
    Nil					(* S ::= Nil                  *)
  | AppExp of IntSyn.exp * spine        (*     | P U                  *) 
  | AppBlock of IntSyn.block * spine    (*     | P rho                *)
  | AppPrg of prg * spine               (*     | P1 P2                *)
  | SClo of spine * sub                 (*     | S [t]                *) 
 
  and sub =				(* Substitutions:             *)
    Shift of int			(* t ::= ^n                   *)
  | Dot of front * sub			(*     | F . t                *)
      
  and front =				(* Fronts:                    *)
    Idx of int		  	        (* F ::= i                    *)
  | Prg of prg				(*     | p                    *)
  | Exp of IntSyn.exp			(*     | U                    *)
  | Block of IntSyn.block		(*     | _x                   *)
  | Undef                               (*     | _                    *)

  and cases =				(* Cases                      *)
    Cases of (dec IntSyn.ctx * sub * prg) list
					(* C ::= (Psi' |> s |-> P)    *)

  datatype con_dec =			(* ConDec                     *)
    ForDec of string * for		(* CD ::= f :: F              *)
  | ValDec of string * prg * for	(*      | f == P              *)

  exception NoMatch
  val coerceSub : sub -> IntSyn.sub
  val embedSub  : IntSyn.sub -> sub
  val coerceCtx : dec IntSyn.ctx -> IntSyn.dec IntSyn.ctx
  val strengthenCtx : dec IntSyn.ctx -> (IntSyn.dec IntSyn.ctx * sub * sub)
  val embedCtx  : IntSyn.dec IntSyn.ctx -> dec IntSyn.ctx
  val weakenSub : dec IntSyn.ctx -> sub
  val invertSub : sub -> sub
  val id        : sub
  val shift     : sub
  val dot1      : sub -> sub
  val dotEta    : front * sub -> sub
  val comp      : sub * sub -> sub
  val varSub    : int * sub -> front
  val decSub    : dec * sub -> dec
  val forSub    : for * sub -> for
  val whnfFor   : for * sub -> for * sub
  val normalizePrg : prg * sub -> prg 
  val normalizeSub : sub -> sub 
  val derefPrg : prg -> prg 
  
  val lemmaLookup : lemma -> con_dec
  val lemmaName   : string -> lemma
  val lemmaAdd    : con_dec -> lemma
  val lemmaSize   : unit -> int
  val lemmaDef    : lemma -> prg
  val lemmaFor    : lemma -> for

  val eqWorlds    : worlds * worlds -> bool

  val convFor     : (for * sub) * (for * sub) -> bool
  val newEVar     : dec IntSyn.ctx * for -> prg
  val newEVarTC   : dec IntSyn.ctx * for * tc option * tc option -> prg 

(* Below are added by Yu Liao *)
  val ctxDec : dec IntSyn.ctx * int -> dec
  val revCoerceSub : IntSyn.sub -> sub
  val revCoerceCtx : IntSyn.dec IntSyn.ctx -> dec IntSyn.ctx

(* Added references by ABP *)
  val coerceFront : front -> IntSyn.front
  val revCoerceFront : IntSyn.front -> front
  val deblockify : IntSyn.dec IntSyn.ctx -> IntSyn.dec IntSyn.ctx * sub

(* Stuff that has to do with termination conditions *)
  val TCSub : tc * IntSyn.sub -> tc
  val normalizeTC : tc -> tc
  val convTC : tc * tc -> bool
  val transformTC : IntSyn.dec IntSyn.ctx * for * int Order.order list -> tc
    

end (* GEN END SIGNATURE DECLARATION *) (* Signature TOMEGA *)




