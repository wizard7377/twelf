(* Delphin external syntax *)


(* GEN BEGIN SIGNATURE DECLARATION *) signature DEXTSYN = 
sig

(* structure Lexer : LEXER *)

datatype ast =  Ast of decs

and decs 
  = Empty
  | FunDecl of fun_decl * decs
  | FormDecl of form_decl * decs
  | ValDecl of val_decl * decs
  | NewDecl of dec * decs
  | TwelfDecl of dec * decs
  | CreateDecl of create_decl * decs

and create_decl
  = Create of term * create_decl
  | Decs of decs

and form_decl 
  = Form of string * form

and fun_decl 
  = Fun of head * prog
  | Bar of head * prog
  | FunAnd of head * prog

and val_decl
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
(* | Arrow of Form * Form *)
(* | WldDef of (string list) * Form *)

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
(* | Rec of MDec * Prog *)

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
  | PatVar of m_dec
  | PatUnderscore 
  | PatUnit 

and m_dec 
  = MDec of string * (form option)

and block 
  = Block of string list

(* and Term 
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
end (* GEN END SIGNATURE DECLARATION *)







