(* Delphin external syntax *)
(* Author: Richard Fontana *)

module DextSyn ( (* module Stream' : STREAM *)
                  module ExtSyn' : EXTSYN
                  module Parsing' : PARSING): DEXTSYN =
(*                    sharing Parsing'.Lexer.Paths = ExtSyn'.Paths  *)
(*                  module Lexer' : LEXER *)
(*                    sharing Lexer' = Parsing'.Lexer *)

struct
(*  module Stream = Stream' *)
  module ExtSyn = ExtSyn'
  module Parsing = Parsing'
(*  module Paths = ExtSyn.Paths
  module Lexer = Lexer' *)
  module L = Lexer
(*  module S = Parsing'.Lexer.Stream *)
  module S = Stream



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
(* | Arrow of form * form *)
(* | WldDef of (string list) * form *)

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
(* | Rec of mDec * prog *)

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



local
(*
let rec parseLFDecs (Ast dl) =
  let let tf = OS.FileSys.tmpName ()
      let tos = TextIO.openOut tf
      let rec parseLFDecs' = function [] -> ()
       | ((LFConDec ld) ::ds) -> 
           (TextIO.output(tos, ld);
           parseLFDecs' ds)
       | (_ ::ds) -> parseLFDecs' ds
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
      let rec rulesToCase' = function [] -> []
      | (ProgDec (Head (s,pts), prg) :: ds) -> 
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
      | (d::ds) -> 
             let let cds = rulesToCase' ds
             in
                (d::cds)
             end

   in
      Ast (rulesToCase' decs)
   end


 (* Invariant:  all programs in ast have been put in case form *)
  let rec abstractProgs' = function [] -> []
    | (ProgDec (Head (nm,e), cp)::ds) -> 
         ProgDec (Head (nm,e), Rec (MDec (nm, NONE), cp))::
                 (abstractProgs' ds)
    | (d::ds) -> (d::(abstractProgs' ds))


 let rec abstractProgs ast =
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
























