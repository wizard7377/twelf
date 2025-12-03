(* Delphin external syntax *)
(* Author: Richard Fontana *)

let recctor DextSyn ( (* module Stream' : STREAM *)
                  module ExtSyn' : EXTSYN
                  module Parsing' : PARSING
(*                    sharing Parsing'.Lexer.Paths = ExtSyn'.Paths  *)
(*                  module Lexer' : LEXER *)
(*                    sharing Lexer' = Parsing'.Lexer *)
      ) : DEXTSYN =

struct
(*  module Stream = Stream' *)
  module ExtSyn = ExtSyn'
  module Parsing = Parsing'
(*  module Paths = ExtSyn.Paths
  module Lexer = Lexer' *)
  module L = Lexer
(*  module S = Parsing'.Lexer.Stream *)
  module S = Stream



type ast =  Ast of Decs

and Decs
  = Empty
  | FunDecl of FunDecl * Decs
  | FormDecl of FormDecl * Decs
  | ValDecl of ValDecl * Decs
  | NewDecl of Dec * Decs
  | TwelfDecl of Dec * Decs
  | CreateDecl of CreateDecl * Decs

and CreateDecl
  = Create of Term * CreateDecl
  | Decs of Decs

and FormDecl
  = Form of string * Form

and FunDecl
  = Fun of Head * Prog
  | Bar of Head * Prog
  | FunAnd of Head * Prog

and ValDecl
  = Val of Pat * Prog * Form option

and Cases
  = First of Pat * Prog
  | Alt of Cases * Pat * Prog


and World =
    WorldIdent of string
  | Plus of World * World
  | Concat of World * World
  | Times of World


and Form
  = True
  | Forall of Dec * Form
  | ForallOmitted of Dec * Form
  | Exists of Dec * Form
  | ExistsOmitted of Dec * Form
  | And of Form * Form
  | World of World * Form
(* | Arrow of Form * Form *)
(* | WldDef of (string list) * Form *)

and Prog
  = Unit
  | Pair of Prog * Prog
  | AppProg of Prog * Prog
  | AppTerm of Prog * Term
  | Inx of Term * Prog
  | Lam of Dec * Prog
  | Par of Prog * Prog
  | Const of string
  | Case of  (Pat list * Prog) list
  | Let of Decs * Prog
  | New of Dec list * Prog
  | Choose of Dec * Prog
(* | Rec of MDec * Prog *)

and Head
  = Head of string
  | AppLF of Head * Term
  | AppMeta of Head * Pat

and Pat
  = PatInx of Term * Pat
  | PatPair of Pat * Pat
  | PatVar of MDec
  | PatUnderscore
  | PatUnit

and MDec
  = MDec of string * (Form option)

and Block
  = Block of string list


(* and Term
  = Term of string
*)
and Term
  = Rtarrow of Term * Term
  | Ltarrow of Term * Term
  | Type
  | Id of string
  | Pi of Dec * Term
  | Fn of Dec * Term
  | App of Term * Term
  | Dot of Term * string
  | Paren of Term
  | Omit
  | Of of Term * Term

and Dec
  = Dec of string * Term



local
(*
let rec parseLFDecs (Ast dl) =
  let let tf = OS.FileSys.tmpName ()
      let tos = TextIO.openOut tf
      fun parseLFDecs' [] = ()
       |  parseLFDecs' ((LFConDec ld) ::ds) =
           (TextIO.output(tos, ld);
           parseLFDecs' ds)
       |  parseLFDecs' (_ ::ds) = parseLFDecs' ds
      let _ = parseLFDecs' dl
      let _ = TextIO.closeOut tos
      let _ = Twelf.loadFile tf
      let _ = OS.FileSys.remove tf
  in ()
  end

*)
(*

let rec rulesToCase (Ast decs) =
   let
      fun rulesToCase' [] = []
      |   rulesToCase' (ProgDec (Head (s,pts), prg) :: ds) =
            let let cds = rulesToCase' ds
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
             let let cds = rulesToCase' ds
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
          let ast' = rulesToCase ast
          let (Ast decs) = ast'
          let decs' = abstractProgs' decs
      in (Ast decs')
      end

*)
in
(*     let appendPats = appendPats
     let parseLFDecs = parseLFDecs
     let abstractProgs = abstractProgs
*)
end

end (* functor DextSyn *)
























