(* Delphin external syntax *)


module type DEXTSYN = 
sig

(* module Lexer : LEXER *)

type ast =  Ast of decs

and decs 
  = Empty
  | FunDecl of funDecl * decs
  | FormDecl of formDecl * decs
  | ValDecl of valDecl * decs
  | NewDecl of dec * decs
  | TwelfDecl of dec * decs
  | CreateDecl of createDecl * decs

and createDecl
  = Create of term * createDecl
  | Decs of decs

and formDecl 
  = Form of string * form

and funDecl 
  = Fun of head * prog
  | Bar of head * prog
  | FunAnd of head * prog

and valDecl
  = Val of pat * prog * form option

and world = 
    WorldIdent of string
  | Plus of world * world
  | Concat of world * world
  | Times of world

and form 
  = True
  | Forall of dec * form
  | ForallOmitted of dec * form
  | Exists of dec * form
  | ExistsOmitted of dec * form
  | And of form * form
  | World of world * form
(* | Arrow of form * form *)
(* | WldDef of (string list) * form *)

and prog 
  = Unit 
  | Pair of prog * prog
  | AppProg of prog * prog
  | AppTerm of prog * term
  | Inx of term * prog 
  | Lam of dec * prog
  | Const of string
  | Case of  (pat list * prog) list
  | Let of decs * prog 
  | Par of prog * prog
  | New of dec list * prog 
  | Choose of dec * prog 
(* | Rec of mDec * prog *)

and cases 
  = First of pat * prog
  | Alt of cases * pat * prog

and head 
  = Head of string
  | AppLF of head * term
  | AppMeta of head * pat

and pat 
  = PatInx of term * pat
  | PatPair of pat * pat
  | PatVar of mDec
  | PatUnderscore 
  | PatUnit 

and mDec 
  = MDec of string * (form option)

and block 
  = Block of string list

(* and term 
  = Term of string
*)
and term 
  = Rtarrow of term * term
  | Ltarrow of term * term
  | Type
  | Id of string
  | Pi of dec * term
  | Fn of dec * term
  | App of term * term
  | Dot of term * string
  | Paren of term
  | Omit
  | Of of term * term

and dec 
  = Dec of string * term
end







