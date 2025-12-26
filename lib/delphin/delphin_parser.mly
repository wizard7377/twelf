%{
(* s is a string consisting of an identifier, followed by one or more
   whitespace characters other than newlines, followed by "::" *)
let chop s =
  let rec stripws s' =
    let last = String.get s' (String.length s' - 1) in
    match last with
    | ' '  -> stripws (String.sub s' 0 (String.length s' - 1))
    | '\t' -> stripws (String.sub s' 0 (String.length s' - 1))
    | _    -> s'
  in
  stripws (String.sub s 0 (String.length s - 2))

(* We'll use the type definitions from Dextsyn module directly *)
open Dextsyn
module L = Lexer

(* For backward compatibility, alias the module *)
module D = Dextsyn
%}

%token <string> ID
%token COLON
%token DOT
%token EQUAL
%token DBLCOLON
%token BLOCKDEC
%token <string> BLOCK
%token CREATE
%token VAL
%token FUN
%token CASE
%token OF
%token BAR
%token LET
%token IN
%token END
%token NEW
%token CHOOSE
%token <string> SOME
%token ALL
%token EXISTS
%token ALLOMITTED
%token EXISTSOMITTED
%token TYPE
%token RTARROW
%token LTARROW
%token RTPAREN
%token LTPAREN
%token RTBRACKET
%token LTBRACKET
%token RTBRACE
%token LTBRACE
%token AND
%token DBLARROW
%token COMMA
%token PAR
%token EOF
%token LTANGLE
%token RTANGLE
%token TRUE
%token UNIT
%token LLAM
%token RLAM
%token AT
%token TIMES
%token PLUS
%token UNDERSCORE
%token WORLD
%token <string> FORMID
%token PREC0
%token PREC1
%token PREC2
%token PREC3

%left PREC0
%left PREC1
%left PREC2
%left PREC3
%left COLON LTARROW
%left AND
%left TIMES
%left PLUS

%right DOT
%right DBLCOLON
%right ID FORMID TRUE ALL EXISTS ALLOMITTED EXISTSOMITTED VAL FUN CASE OF BAR LET CREATE IN END NEW CHOOSE
%right RTARROW DBLARROW

%nonassoc PAR UNDERSCORE AT
%nonassoc LTPAREN RTPAREN LTBRACE RTBRACE LTBRACKET RTBRACKET LLAM RLAM
%nonassoc LTANGLE RTANGLE

%start start
%type <Dextsyn.ast> start

%%

start:
  | decs %prec PREC0
    { D.Ast $1 }

decs:
  | %prec PREC1
    { D.Empty }
  | fundecl decs %prec PREC1
    { D.FunDecl ($1, $2) }
  | formdecl decs %prec PREC1
    { D.FormDecl ($1, $2) }
  | valdecl decs %prec PREC1
    { D.ValDecl ($1, $2) }
  | NEW LTPAREN dec RTPAREN decs %prec PREC1
    { D.NewDecl ($3, $5) }
  | dec decs %prec PREC1
    { D.TwelfDecl ($1, $2) }
  | createdecl decs %prec PREC1
    { D.CreateDecl ($1, $2) }

createdecl:
  | CREATE term createdecl %prec PREC2
    { D.Create ($2, $3) }
  | valdecl END %prec PREC2
    { D.Decs (D.ValDecl($1, D.Empty)) }

formdecl:
  | FORMID form %prec PREC2
    { D.Form (chop $1, $2) }

fundecl:
  | FUN head EQUAL prog %prec PREC2
    { D.Fun ($2, $4) }
  | BAR head EQUAL prog %prec PREC2
    { D.Bar ($2, $4) }
  | AND head EQUAL prog %prec PREC2
    { D.FunAnd ($2, $4) }

valdecl:
  | VAL pat DBLCOLON form EQUAL prog %prec PREC2
    { D.Val ($2, $6, Some $4) }
  | VAL pat EQUAL prog %prec PREC2
    { D.Val ($2, $4, None) }

term:
  | TYPE %prec PREC3
    { D.Type }
  | ID %prec PREC3
    { D.Id (chop $1) }
  | TRUE %prec PREC3
    { D.Id "true" }
  | AND %prec PREC3
    { D.Id "and" }
  | ALL %prec PREC3
    { D.Id "all" }
  | ALLOMITTED %prec PREC3
    { D.Id "all^" }
  | EXISTS %prec PREC3
    { D.Id "exists" }
  | EXISTSOMITTED %prec PREC3
    { D.Id "exists^" }
  | VAL %prec PREC3
    { D.Id "val" }
  | FUN %prec PREC3
    { D.Id "fun" }
  | CASE %prec PREC3
    { D.Id "case" }
  | OF %prec PREC3
    { D.Id "of" }
  | PAR %prec PREC3
    { D.Id "||" }
  | BAR %prec PREC3
    { D.Id "|" }
  | LET %prec PREC3
    { D.Id "let" }
  | TIMES %prec PREC3
    { D.Id "*" }
  | PLUS %prec PREC3
    { D.Id "+" }
  | IN %prec PREC3
    { D.Id "in" }
  | END %prec PREC3
    { D.Id "end" }
  | NEW %prec PREC3
    { D.Id "new" }
  | CHOOSE %prec PREC3
    { D.Id "choose" }
  | term RTARROW term %prec PREC3
    { D.Rtarrow ($1, $3) }
  | term LTARROW term %prec PREC3
    { D.Ltarrow ($1, $3) }
  | LTBRACE dec RTBRACE term %prec PREC3
    { D.Pi ($2, $4) }
  | LTBRACKET dec RTBRACKET term %prec PREC3
    { D.Fn ($2, $4) }
  | LTPAREN term RTPAREN %prec PREC3
    { D.Paren $2 }
  | ID term %prec PREC3
    { D.App (D.Id $1, $2) }
  | TRUE term %prec PREC3
    { D.App (D.Id "true", $2) }
  | AND term %prec PREC3
    { D.App (D.Id "and", $2) }
  | ALL term %prec PREC3
    { D.App (D.Id "all", $2) }
  | ALLOMITTED term %prec PREC3
    { D.App (D.Id "all^", $2) }
  | EXISTS term %prec PREC3
    { D.App (D.Id "exists", $2) }
  | EXISTSOMITTED term %prec PREC3
    { D.App (D.Id "exists^", $2) }
  | VAL term %prec PREC3
    { D.App (D.Id "val", $2) }
  | FUN term %prec PREC3
    { D.App (D.Id "fun", $2) }
  | CASE term %prec PREC3
    { D.App (D.Id "case", $2) }
  | OF term %prec PREC3
    { D.App (D.Id "of", $2) }
  | BAR term %prec PREC3
    { D.App (D.Id "|", $2) }
  | PAR term %prec PREC3
    { D.App (D.Id "||", $2) }
  | LET term %prec PREC3
    { D.App (D.Id "let", $2) }
  | IN term %prec PREC3
    { D.App (D.Id "in", $2) }
  | END term %prec PREC3
    { D.App (D.Id "end", $2) }
  | NEW term %prec PREC3
    { D.App (D.Id "new", $2) }
  | CHOOSE term %prec PREC3
    { D.App (D.Id "choose", $2) }
  | UNDERSCORE term %prec PREC3
    { D.Omit }
  | LTPAREN term RTPAREN term %prec PREC3
    { D.App (D.Paren $2, $4) }
  | term COLON term %prec PREC3
    { D.Of ($1, $3) }
  | UNDERSCORE %prec PREC3
    { D.Omit }
  | term DOT ID %prec PREC3
    { D.Dot ($1, $3) }

world:
  | LTPAREN world RTPAREN %prec PREC1
    { $2 }
  | ID %prec PREC1
    { D.WorldIdent $1 }
  | world world %prec PREC1
    { D.Concat ($1, $2) }
  | world PLUS world %prec PREC1
    { D.Plus ($1, $3) }
  | world TIMES %prec PREC1
    { D.Times $1 }

dec:
  | ID COLON term %prec PREC1
    { D.Dec ($1, $3) }
  | ID %prec PREC1
    { D.Dec ($1, D.Omit) }

form:
  | WORLD world form %prec PREC0
    { D.World ($2, $3) }
  | ALL LTBRACE dec RTBRACE form %prec PREC0
    { D.Forall ($3, $5) }
  | ALLOMITTED LTBRACE dec RTBRACE form %prec PREC0
    { D.ForallOmitted ($3, $5) }
  | EXISTS LTBRACE dec RTBRACE form %prec PREC0
    { D.Exists ($3, $5) }
  | EXISTSOMITTED LTBRACE dec RTBRACE form %prec PREC0
    { D.ExistsOmitted ($3, $5) }
  | form AND form %prec PREC0
    { D.And ($1, $3) }
  | LTPAREN form RTPAREN %prec PREC0
    { $2 }
  | TRUE %prec PREC0
    { D.True }

prog:
  | ID
    { D.Const $1 }
  | prog ID
    { D.AppTerm ($1, D.Id $2) }
  | prog UNDERSCORE
    { D.AppTerm ($1, D.Id "_") }
  | prog LTPAREN term RTPAREN
    { D.AppTerm ($1, $3) }
  | LTPAREN prog RTPAREN
    { $2 }
  | UNIT
    { D.Unit }
  | CASE prog OF cases
    { D.Unit }
  | prog PAR prog
    { D.Par ($1, $3) }
  | LTPAREN prog COMMA prog RTPAREN
    { D.Pair ($2, $4) }
  | prog AT prog
    { D.AppProg ($1, $3) }
  | LTANGLE term COMMA prog RTANGLE
    { D.Inx ($2, $4) }
  | LLAM dec RLAM prog
    { D.Lam ($2, $4) }
  | LET decs IN prog END
    { D.Let ($2, $4) }
  | NEW lfdecs IN prog END
    { D.New ($2, $4) }
  | CHOOSE LTPAREN dec RTPAREN IN prog END
    { D.Choose ($3, $6) }

lfdecs:
  |
    { [] }
  | LTPAREN dec RTPAREN lfdecs
    { $2 :: $4 }

cases:
  | pat DBLARROW prog %prec PREC0
    { D.First ($1, $3) }
  | cases BAR pat DBLARROW prog %prec PREC1
    { D.Alt ($1, $3, $5) }

head:
  | ID
    { D.Head $1 }
  | head ID
    { D.AppLF ($1, D.Id $2) }
  | head UNDERSCORE
    { D.AppLF ($1, D.Omit) }
  | head LTPAREN term RTPAREN
    { D.AppLF ($1, $3) }
  | head AT pat
    { D.AppMeta ($1, $3) }

mdec:
  | ID
    { D.MDec ($1, None) }
  | FORMID form
    { D.MDec (chop $1, Some $2) }

pat:
  | mdec
    { D.PatVar $1 }
  | LTPAREN pat COMMA pat RTPAREN
    { D.PatPair ($2, $4) }
  | LTANGLE term COMMA pat RTANGLE
    { D.PatInx ($2, $4) }
  | UNIT
    { D.PatUnit }
  | UNDERSCORE
    { D.PatUnderscore }
