(* Delphin external syntax *)
(* Author: Richard Fontana *)

functor (* GEN BEGIN FUNCTOR DECL *) DextSyn ( (* structure Stream' : STREAM *)
                  structure ExtSyn' : EXTSYN
                  structure Parsing' : PARSING
(*                    sharing Parsing'.Lexer.Paths = ExtSyn'.Paths  *)
(*                  structure Lexer' : LEXER *)
(*                    sharing Lexer' = Parsing'.Lexer *)
      ) : DEXTSYN =

struct
(*  structure Stream = Stream' *)
  structure ExtSyn = ExtSyn'
  structure Parsing = Parsing'
(*  structure Paths = ExtSyn.Paths
  structure Lexer = Lexer' *)
  structure L = Lexer
(*  structure S = Parsing'.Lexer.Stream *)
  structure S = Stream



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

and cases
  = First of pat * prog
  | Alt of cases * pat * prog


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
  | Par of prog * prog
  | Const of string
  | Case of  (pat list * prog) list
  | Let of decs * prog
  | New of dec list * prog
  | Choose of dec * prog
(* | Rec of MDec * Prog *)

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



local
(*
fun parseLFDecs (Ast dl) =
  let val tf = OS.FileSys.tmpName ()
      val tos = TextIO.openOut tf
      fun parseLFDecs' [] = ()
       |  parseLFDecs' ((LFConDec ld) ::ds) =
           (TextIO.output(tos, ld);
           parseLFDecs' ds)
       |  parseLFDecs' (_ ::ds) = parseLFDecs' ds
      val _ = parseLFDecs' dl
      val _ = TextIO.closeOut tos
      val _ = Twelf.loadFile tf
      val _ = OS.FileSys.remove tf
  in ()
  end

*)
(*

fun rulesToCase (Ast decs) =
   let
      fun rulesToCase' [] = []
      |   rulesToCase' (ProgDec (Head (s,pts), prg) :: ds) =
            let val cds = rulesToCase' ds
            in
               case cds of
                  ProgDec (Head (s',_), Case ps) ::ds'' =>
                     if s = s'
                     then ProgDec (Head (s, []), Case ((pts,prg)::ps))::ds''
                     else
                         ProgDec (Head (s,[]), Case [(pts,prg)]):: cds
                | _ => ProgDec (Head (s,[]), Case [(pts,prg)]):: cds
             end
      |   rulesToCase' (d::ds) =
             let val cds = rulesToCase' ds
             in
                (d::cds)
             end

   in
      Ast (rulesToCase' decs)
   end


 (* Invariant:  all programs in ast have been put in case form *)
  fun abstractProgs' [] = []
    | abstractProgs' (ProgDec (Head (nm,e), cp)::ds) =
         ProgDec (Head (nm,e), Rec (MDec (nm, NONE), cp))::
                 (abstractProgs' ds)
    | abstractProgs' (d::ds) = (d::(abstractProgs' ds))


 fun abstractProgs ast =
      let
          val ast' = rulesToCase ast
          val (Ast decs) = ast'
          val decs' = abstractProgs' decs
      in (Ast decs')
      end

*)
in
(*     val appendPats = appendPats
     val parseLFDecs = parseLFDecs
     val abstractProgs = abstractProgs
*)
end

end (* GEN END FUNCTOR DECL *) (* functor DextSyn *)
























