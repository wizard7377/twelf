(* Printing *)

(* Author: Frank Pfenning *)

(* Modified: Jeff Polakow *)

module type PRINT = sig
  (*! structure IntSyn : Intsyn.INTSYN !*)
  module Formatter : Formatter.FORMATTER

  val implicit : bool ref
  val printInfix : bool ref
  val printDepth : int option ref
  val printLength : int option ref
  val noShadow : bool ref
  val formatDec : IntSyn.dctx * IntSyn.dec -> Formatter.format
  val formatDecList : IntSyn.dctx * IntSyn.dec list -> Formatter.format

  val formatDecList' :
    IntSyn.dctx * (IntSyn.dec list * IntSyn.sub) -> Formatter.format

  val formatExp : IntSyn.dctx * IntSyn.exp -> Formatter.format
  val formatSpine : IntSyn.dctx * IntSyn.spine -> Formatter.format list
  val formatConDec : IntSyn.conDec -> Formatter.format
  val formatConDecI : IntSyn.conDec -> Formatter.format
  val formatCnstr : IntSyn.cnstr -> Formatter.format
  val formatCtx : IntSyn.dctx * IntSyn.dctx -> Formatter.format
  val decToString : IntSyn.dctx * IntSyn.dec -> string
  val expToString : IntSyn.dctx * IntSyn.exp -> string
  val conDecToString : IntSyn.conDec -> string
  val cnstrToString : IntSyn.cnstr -> string
  val cnstrsToString : IntSyn.cnstr list -> string

  (* assigns names in contexts *)
  val ctxToString : IntSyn.dctx * IntSyn.dctx -> string
  val evarInstToString : IntSyn.exp * string list -> string
  val evarCnstrsToStringOpt : IntSyn.exp * string list -> string option
  val formatWorlds : Tomega.worlds -> Formatter.format
  val worldsToString : Tomega.worlds -> string
  val printSgn : unit -> unit
end

(* signature PRINT *)
(* Printing *)


(* Author: Frank Pfenning *)


(* Modified: Jeff Polakow, Roberto Virga *)


module Print (Whnf : Whnf.WHNF) (Abstract : Abstract.ABSTRACT) (Constraints : Constraints.CONSTRAINTS) (Names : Names.NAMES) (Formatter' : Formatter.FORMATTER) (Symbol : Symbol.SYMBOL) : PRINT = struct (*! structure IntSyn = IntSyn' !*)

module Formatter = Formatter'
module Tomega = Tomega
(* Externally visible parameters *)

let implicit = ref (false)
(* whether to print implicit arguments *)

let printInfix = ref (false)
(* if implicit is ref true, whether to print infix ops when possible *)

let printDepth = ref ((None : int option))
(* limit on term depth to print *)

let printLength = ref ((None : int option))
(* limit on number of arguments to print *)

let noShadow = ref (false)
(* if true, don't print shadowed "%const%" *)

(* Shorthands *)

module I = IntSyn
module FX = NamesFixity
module F = Formatter
module T = Tomega
(* Disambiguation of block logic variable names *)

let lvars : I.block option ref list ref = ref []
let rec lookuplvar (l)  = ( (* speed improvment possible Tue Mar  1 13:27:04 2011 --cs *)
let _ = if (List.exists (fun r -> r = l) (! lvars)) then () else lvars := ! lvars @ [l] in let rec find (r :: L) n  = if r = l then n else find L (n + 1) in  Int.toString (find (! lvars) 0) )
let Str = F.String
let rec Str0 (s, n)  = F.string0 n s
let rec sym (s)  = Str0 (Symbol.sym s)
let rec nameOf = function (Some (id)) -> id | (None) -> "_"
(* fmtEVar (G, X) = "X", the name of the EVar X *)

(* Effect: Names.evarName will assign a name if X does not yet have one *)

let rec fmtEVar (G, X)  = Str0 (Symbol.evar (Names.evarName (G, X)))
(* should probably be a new Symbol constructor for_sml AVars -kw *)

let rec fmtAVar (G, X)  = Str0 (Symbol.evar (Names.evarName (G, X) ^ "_"))
(* isNil S = true iff S == Nil *)

let rec isNil = function (I.Nil) -> true | (I.App _) -> false | (I.SClo (S, _)) -> isNil S
(* subToSpine (depth, s) = S
     Invariants:
     If  G |- s : G', Gd  with  |Gd| = depth
     then G |- S : {{Gd}} C > C  for_sml any C

     This is used to print
      G |- Xl[s] : A[s]  for_sml  G', Gd |- Xl : G |- Xr @ S : A[s]  for_sml  G' |- Xr : {{Gd}} A
     where Xr is the raised version of Xl.
     Xr is not actually created, just printed using the name of Xl.
  *)

let rec subToSpine (depth, s)  = ( let rec sTS = function (I.Shift (k), S) -> if k < depth then sTS (I.Dot (I.Idx (k + 1), I.Shift (k + 1)), S) else (* k >= depth *)
S | (I.Dot (I.Idx (k), s), S) -> sTS (s, I.App (I.Root (I.BVar (k), I.Nil), S)) | (I.Dot (I.Exp (U), s), S) -> sTS (s, I.App (U, S)) in  sTS (s, I.Nil) )
(* ArgStatus classifies the number of arguments to an operator *)

type argStatus = TooFew | Exact of I.spine | TooMany of I.spine * I.spine
let rec sclo' = function (TooFew, s) -> TooFew | (Exact (S), s) -> Exact (I.SClo (S, s)) | (TooMany (S, S'), s) -> TooMany (I.SClo (S, s), I.SClo (S', s))
let rec sclo'' = function (TooFew, s) -> TooFew | (Exact (S), s) -> Exact (S) | (TooMany (S, S'), s) -> TooMany (S, I.SClo (S', s))
(* dropImp (i, S, n) for_sml n >= 1
     = TooFew            if |S| < i+n
     = Exact(S')         if n >= 1, |S| = i+n, S = _ @ S' and |S'| = n
                         if n = 0, |S| = _ @ S', |_| = i
     = TooMany(S', S'')  if n >=1, |S| > i+n, S = _ @ S' and |S'| > n,
                                              S' = S0 @ S'' and |S0| = n
  *)

let rec dropImp = function (0, S, 0) -> Exact (S) | (0, S, n) -> ( let rec checkArgNumber = function (I.Nil, 0) -> Exact (S) | (I.Nil, k) -> TooFew | (S', 0) -> TooMany (S, S') | (I.App (U, S'), k) -> checkArgNumber (S', k - 1) | (I.SClo (S', s), k) -> sclo'' (checkArgNumber (S', k), s) in  checkArgNumber (S, n) ) | (i, I.App (U, S), n) -> dropImp (i - 1, S, n) | (i, I.SClo (S, s), n) -> sclo' (dropImp (i, S, n), s) | (i, I.Nil, n) -> TooFew
(* exceeded (n:int, b:bound) = true if n exceeds bound b *)

let rec exceeded = function (_, None) -> false | ((n : int), (Some (m : int))) -> n >= m
(* Type ctxt is the "left context" of an expression to be printed.
     It an accumulator and is used to decide whether to insert of parentheses
     or elide nested subexpressions.

     Ctxt (fixity, formats, length)
     is the "left context" of an expression to be printed.  When printed
     it will be the string prefixed to the string representing the
     current expression.

     fixity is the operator and precedence in effect,
     formats is the list of formats which make up the left context
     length is the length of the left context (used for_sml printLength elision)
  *)

type ctxt = Ctxt of FX.fixity * F.format list * int
(* Type opargs represent the operator/arguments form of roots.

     OpArgs (fixity, formats, S)
     represents the printed form of a root expression H @ S:
      fixity is the fixity of H (possibly FX.Nonfix),
      formats is a list of formats for_sml printing H (including surrounding breaks
         and whitespace),
      S is the spine of arguments.
      There may be additional argument in S which are ignored.

     EtaLong (U)
     represents an expression U' which had to be eta-expanded to U
     in order to supply enough arguments to a prefix, postfix, or infix operator
     so it can be printed.
  *)

type opargs = OpArgs of FX.fixity * F.format list * I.spine | EtaLong of I.exp
let noCtxt = Ctxt (FX.Prefix (FX.dec (FX.dec (FX.dec (FX.dec FX.minPrec)))), [], 0)
(* empty left context *)

let binderPrec = FX.dec (FX.dec (FX.dec FX.minPrec))
(* braces and a prefix operator *)

(* colon is of FX.minPrec-2, but doesn't occur in printing *)

let arrowPrec = FX.dec FX.minPrec
(* infix operator *)

let juxPrec = FX.inc FX.maxPrec
(* infix operator *)

(* arrow (V1, V2) = oa
     where oa is the operator/argument representation of V1 -> V2
  *)

let rec arrow (V1, V2)  = OpArgs (FX.Infix (arrowPrec, FX.Right), [F.Break; sym "->"; F.Space], I.App (V1, I.App (V2, I.Nil)))
(* Nonfix corresponds to application and therefore has precedence juxPrex (which is maximal) *)

let appCtxt = Ctxt (FX.Nonfix, [], 0)
(* fixityCon (c) = fixity of c *)

let rec fixityCon = function (I.Const (cid)) -> Names.getFixity (cid) | (I.Skonst (cid)) -> FX.Nonfix | (I.Def (cid)) -> Names.getFixity (cid) | (I.NSDef (cid)) -> Names.getFixity (cid) | _ -> FX.Nonfix
(* BVar, FVar *)

(* impCon (c) = number of implicit arguments to c *)

let rec impCon = function (I.Const (cid)) -> I.constImp (cid) | (I.Skonst (cid)) -> I.constImp (cid) | (I.Def (cid)) -> I.constImp (cid) | (I.NSDef (cid)) -> I.constImp (cid) | _ -> 0
(* BVar, FVar *)

(* argNumber (fixity) = number of required arguments to head with fixity *)

let rec argNumber = function (FX.Nonfix) -> 0 | (FX.Infix _) -> 2 | (FX.Prefix _) -> 1 | (FX.Postfix _) -> 1
(* FIX: this is certainly not correct -kw *)

let rec fmtConstPath (f, Names.Qid (ids, id))  = F.HVbox (foldr (fun (id, fmt) -> Str0 (Symbol.str (id)) :: sym "." :: fmt) [Str0 (f (id))] ids)
let rec parmDec = function (D :: L, 1) -> D | (D :: L, j) -> parmDec (L, j - 1)
let rec parmName (cid, i)  = ( let (Gsome, Gblock) = I.constBlock (cid) in  match parmDec (Gblock, i) with I.Dec (Some (pname), _) -> pname | I.Dec (None, _) -> Int.toString i )
let rec projName = function (G, I.Proj (I.Bidx (k), i)) -> ( (* names should have been assigned by invar
         iant, NONE imppossible *)
let I.BDec (Some (bname), (cid, t)) = I.ctxLookup (G, k) in  bname ^ "_" ^ parmName (cid, i) ) | (G, I.Proj (I.LVar (r, _, (cid, t)), i)) -> "_" ^ parmName (cid, i) | (G, I.Proj (I.Inst iota, i)) -> "*"
(* to be fixed --cs *)

let rec constQid (cid)  = if ! noShadow then Names.conDecQid (I.sgnLookup cid) else Names.constQid cid
let rec cidToFmt (cid)  = F.String (Names.qidToString (Names.constQid cid))
let rec formatCids = function ([]) -> [] | (cid :: []) -> [cidToFmt cid] | (cid :: cids) -> cidToFmt cid :: F.Break :: F.String "|" :: F.Space :: formatCids cids
let rec formatWorlds (T.Worlds cids)  = F.Hbox [F.String "("; F.HVbox (formatCids cids); F.String ")"]
let rec worldsToString (W)  = F.makestring_fmt (formatWorlds W)
(* fmtCon (c) = "c" where the name is assigned according the the Name table
     maintained in the names module.
     FVar's are printed with a preceding "`" (backquote) character
  *)

let rec fmtCon = function (G, I.BVar (n)) -> Str0 (Symbol.bvar (Names.bvarName (G, n))) | (G, I.Const (cid)) -> fmtConstPath (Symbol.const, constQid (cid)) | (G, I.Skonst (cid)) -> fmtConstPath (Symbol.skonst, constQid (cid)) | (G, I.Def (cid)) -> fmtConstPath (Symbol.def, constQid (cid)) | (G, I.NSDef (cid)) -> fmtConstPath (Symbol.def, constQid (cid)) | (G, I.FVar (name, _, _)) -> Str0 (Symbol.fvar (name)) | (G, H) -> Str0 (Symbol.const (projName (G, H))) | (G, H) -> ( let n = lookuplvar (r) in  (* LVar fixed Sun Dec  1 11:36:55 2002 -cs *)
fmtConstPath (fun l0 -> Symbol.const ("#[" ^ l0 ^ n ^ "]" ^ projName (G, H)), constQid (cid)) ) | (G, I.FgnConst (cs, conDec)) -> ( (* will need to be changed if qualified constraint constant
             names are introduced... anyway, why should the user be
             allowed to shadow constraint constants? -kw *)
let name = I.conDecName conDec in  match (Names.constLookup (Names.Qid ([], name)), ! noShadow) with (Some _, false) -> (* the user has re-defined this name *)
Str0 (Symbol.const ("%" ^ name ^ "%")) | _ -> Str0 (Symbol.const name) )
(* evarArgs (G, d, X, s)
     formats X[s] by printing X @ S, where S is the substitution s in spine form.
     This is an implicit form of raising.
  *)

let rec evarArgs (G, d, X, s)  = OpArgs (FX.Nonfix, [fmtEVar (G, X)], subToSpine (I.ctxLength (G), s))
let rec evarArgs' (G, d, X, s)  = OpArgs (FX.Nonfix, [fmtAVar (G, X)], subToSpine (I.ctxLength (G), s))
(* fst (S, s) = U1, the first argument in S[s] *)

let rec fst = function (I.App (U1, _), s) -> (U1, s) | (I.SClo (S, s'), s) -> fst (S, I.comp (s', s))
(* snd (S, s) = U2, the second argument in S[s] *)

let rec snd = function (I.App (U1, S), s) -> fst (S, s) | (I.SClo (S, s'), s) -> snd (S, I.comp (s', s))
(* elide (l) = true  iff  l exceeds the optional printLength bound *)

let rec elide (l)  = match ! printLength with None -> false | Some (l') -> (l > l')
let ldots = sym "..."
(* addots (l) = true  iff  l is equal to the optional printLength bound *)

let rec addots (l)  = match ! printLength with None -> false | Some (l') -> (l = l')
(* parens ((fixity', fixity), fmt) = fmt'
     where fmt' contains additional parentheses when the precedence of
     fixity' is greater or equal to that of fixity, otherwise it is unchanged.
  *)

let rec parens ((fixity', fixity), fmt)  = if FX.leq (FX.prec (fixity), FX.prec (fixity')) then F.Hbox [sym "("; fmt; sym ")"] else fmt
(* eqFix (fixity, fixity') = true iff fixity and fixity' have the same precedence
     Invariant: only called when precedence comparison is necessary to resolve
                the question if parentheses should be added
  *)

let rec eqFix = function (FX.Infix (p, FX.Left), FX.Infix (p', FX.Left)) -> (p = p') | (FX.Infix (p, FX.Right), FX.Infix (p', FX.Right)) -> (p = p') | (FX.Prefix (p), FX.Prefix (p')) -> (p = p') | (FX.Postfix (p), FX.Postfix (p')) -> (p = p') | _ -> false
(* addAccum (fmt, fixity, accum) = fmt'
     Extend the current "left context" with operator fixity
     and format list accum by fmt.

     This is not very efficient, since the accumulator is copied
     for_sml right associative or prefix operators.
  *)

let rec addAccum = function (fmt, _, []) -> fmt | (fmt, FX.Infix (_, FX.Left), accum) -> F.HVbox ([fmt] @ accum) | (fmt, FX.Infix (_, FX.Right), accum) -> F.HVbox (accum @ [fmt]) | (fmt, FX.Prefix _, accum) -> F.HVbox (accum @ [fmt]) | (fmt, FX.Postfix _, accum) -> F.HVbox ([fmt] @ accum)
(* FX.Infix(None,_), FX.Nonfix should never arise *)

(* aa (ctx, fmt) = fmt'
     Extend the current "left context" by fmt.
  *)

let rec aa (Ctxt (fixity, accum, l), fmt)  = addAccum (fmt, fixity, accum)
(* fmtUni (L) = "L" *)

let rec fmtUni = function (I.Type) -> sym "type" | (I.Kind) -> sym "kind"
(* impossible, included for_sml robustness *)

(* fmtExpW (G, d, ctx, (U, s)) = fmt

     format the expression U[s] at printing depth d and add it to the left context
     ctx.

     Invariants:
       G is a "printing context" (names in it are unique, but
            types may be incorrect) approximating G'
       G'' |- U : V   G' |- s : G''  (so  G' |- U[s] : V[s])
       (U,s) in whnf
  *)

let rec fmtExpW = function (G, d, ctx, (I.Uni (L), s)) -> aa (ctx, fmtUni (L)) | (G, d, ctx, (I.Pi ((D, P), V2), s)) -> (match P(* if Pi is dependent but anonymous, invent name here *)
 with I.Maybe -> ( (* could sometimes be EName *)
let D' = Names.decLUName (G, D) in  fmtLevel (I.Decl (G, D')(* I.decSub (D', s) *)
, d, ctx, (braces (G, d, ((D', V2), s)), I.dot1 s)) ) | I.Meta -> ( let D' = Names.decLUName (G, D) in  fmtLevel (I.Decl (G, D')(* I.decSub (D', s) *)
, d, ctx, (braces (G, d, ((D', V2), s)), I.dot1 s)) ) | I.No -> fmtLevel (I.Decl (G, D)(* I.decSub (D, s) *)
, d, ctx, (arrow (I.EClo (V1, I.shift), V2), I.dot1 s))) | (G, d, ctx, (I.Pi ((D, P), V2), s)) -> ( let D' = Names.decLUName (G, D) in  fmtLevel (I.Decl (G, D'), d, ctx, (braces (G, d, ((D', V2), s)), I.dot1 s)) ) | (G, d, ctx, (I.Pi ((D, P), V2), s)) -> ( (*      val D' = Names.decLUName (G, D) *)
let braces = OpArgs (FX.Prefix (binderPrec), [sym "["; sym "_"; sym "]"; F.Break], IntSyn.App (V2, IntSyn.Nil)) in  fmtLevel (I.Decl (G, D), d, ctx, (braces, I.dot1 s)) ) | (G, d, ctx, (U, s)) -> fmtOpArgs (G, d, ctx, opargs (G, d, R), s) | (G, d, ctx, (I.Lam (D, U), s)) -> ( let D' = Names.decLUName (G, D) in  fmtLevel (I.Decl (G, D')(* I.decSub (D', s) *)
, d, ctx, (brackets (G, d, ((D', U), s)), I.dot1 s)) ) | (G, d, ctx, (X, s)) -> if ! implicit then aa (ctx, F.HVbox (fmtEVar (G, X) :: fmtSub (G, d, s))) else fmtOpArgs (G, d, ctx, evarArgs (G, d, X, s), I.id) | (G, d, ctx, (X, s)) -> if ! implicit then aa (ctx, F.HVbox (fmtAVar (G, X) :: fmtSub (G, d, s))) else fmtOpArgs (G, d, ctx, evarArgs' (G, d, X, s), I.id) | (G, d, ctx, (U, s)) -> fmtExp (G, d, ctx, (I.FgnExpStd.ToInternal.apply csfe (), s))
and opargsImplicit (G, d, (C, S))  = OpArgs (FX.Nonfix, [fmtCon (G, C)], S)
and opargsImplicitInfix (G, d, R)  = ( let fixity = fixityCon C in  match fixity with FX.Infix _ -> opargsExplicit (G, d, R)(* Can't have implicit arguments by invariant *)
 | _ -> OpArgs (FX.Nonfix, [fmtCon (G, C)], S) )
and opargsExplicit (G, d, R)  = ( let opFmt = fmtCon (G, C) in let fixity = fixityCon C in let rec oe = function (Exact (S')) -> (match fixity with FX.Nonfix -> OpArgs (FX.Nonfix, [opFmt], S') | FX.Prefix _ -> OpArgs (fixity, [opFmt; F.Break], S') | FX.Postfix _ -> OpArgs (fixity, [F.Break; opFmt], S') | FX.Infix _ -> OpArgs (fixity, [F.Break; opFmt; F.Space], S')) | (TooFew) -> EtaLong (Whnf.etaExpandRoot (I.Root R)) | (TooMany (S', S'')) -> ( let opFmt' = fmtOpArgs (G, d, noCtxt, oe (Exact (S')), I.id) in  (* parens because juxtaposition has highest precedence *)
(*
                 could be redundant for_sml prefix or postfix operators, but
                 include anyway to avoid misreading output
              *)
OpArgs (FX.Nonfix, [F.Hbox [sym "("; opFmt'; sym ")"]], S'') ) in  oe (dropImp (impCon C, S, argNumber fixity)) )
and opargs (G, d, R)  = if ! implicit then if ! printInfix then opargsImplicitInfix (G, d, R) else opargsImplicit (G, d, R) else opargsExplicit (G, d, R)
and fmtOpArgs = function (G, d, ctx, oa, s) -> if isNil S' then aa (ctx, List.hd opFmts)(* opFmts = [fmtCon(G,C)] *)
 else fmtLevel (G, d, ctx, (oa, s)) | (G, d, ctx, EtaLong (U'), s) -> fmtExpW (G, d, ctx, (U', s))
and fmtSub (G, d, s)  = Str "[" :: fmtSub' (G, d, 0, s)
and fmtSub' (G, d, l, s)  = if elide l then [ldots] else fmtSub'' (G, d, l, s)
and fmtSub'' = function (G, d, l, I.Shift (k)) -> [Str ("^" ^ Int.toString k); Str "]"] | (G, d, l, I.Dot (I.Idx (k), s)) -> Str (Names.bvarName (G, k)) :: Str "." :: F.Break :: fmtSub' (G, d, l + 1, s) | (G, d, l, I.Dot (I.Exp (U), s)) -> fmtExp (G, d + 1, noCtxt, (U, I.id)) :: Str "." :: F.Break :: fmtSub' (G, d, l + 1, s)
and fmtExp (G, d, ctx, (U, s))  = if exceeded (d, ! printDepth) then sym "%%" else fmtExpW (G, d, ctx, Whnf.whnf (U, s))
and fmtSpine = function (G, d, l, (I.Nil, _)) -> [] | (G, d, l, (I.SClo (S, s'), s)) -> fmtSpine (G, d, l, (S, I.comp (s', s))) | (G, d, l, (I.App (U, S), s)) -> if elide (l) then [](* necessary? *)
 else if addots (l) then [ldots] else fmtExp (G, d + 1, appCtxt, (U, s)) :: fmtSpine' (G, d, l, (S, s))
and fmtSpine' = function (G, d, l, (I.Nil, _)) -> [] | (G, d, l, (I.SClo (S, s'), s)) -> fmtSpine' (G, d, l, (S, I.comp (s', s))) | (G, d, l, (S, s)) -> F.Break :: fmtSpine (G, d, l + 1, (S, s))
and fmtLevel = function (G, d, Ctxt (fixity', accum, l), (OpArgs (fixity, fmts, S), s)) -> ( (* atm must not be empty, otherwise bug below *)
let atm = fmtSpine (G, d, 0, (S, s)) in  (* F.HVbox doesn't work if last item of HVbox is F.Break *)
addAccum (parens ((fixity', fixity), F.HVbox (fmts @ [F.Break] @ atm)), fixity', accum)(* possible improvement along the following lines: *)
(*
           if (#2 (F.Width (F.Hbox (fmts)))) < 4
           then F.Hbox [F.Hbox(fmts), F.HVbox0 1 1 1 atm]
           else ...
        *)
 ) | (G, d, Ctxt (fixity', accum, l), (OpArgs (fixity, fmts, S), s)) -> ( let accMore = eqFix (fixity, fixity') in let rhs = if accMore && elide (l) then [] else if accMore && addots (l) then fmts @ [ldots] else fmts @ [fmtExp (G, d + 1, Ctxt (FX.Infix (p, FX.None), [], 0), snd (S, s))] in  if accMore then fmtExp (G, d, Ctxt (fixity, rhs @ accum, l + 1), fst (S, s)) else ( let both = fmtExp (G, d, Ctxt (fixity, rhs, 0), fst (S, s)) in  addAccum (parens ((fixity', fixity), both), fixity', accum) ) ) | (G, d, Ctxt (fixity', accum, l), (OpArgs (fixity, fmts, S), s)) -> ( let accMore = eqFix (fixity, fixity') in let lhs = if accMore && elide (l) then [] else if accMore && addots (l) then [ldots] @ fmts else [fmtExp (G, d + 1, Ctxt (FX.Infix (p, FX.None), [], 0), fst (S, s))] @ fmts in  if accMore then fmtExp (G, d, Ctxt (fixity, accum @ lhs, l + 1), snd (S, s)) else ( let both = fmtExp (G, d, Ctxt (fixity, lhs, 0), snd (S, s)) in  addAccum (parens ((fixity', fixity), both), fixity', accum) ) ) | (G, d, Ctxt (fixity', accum, l), (OpArgs (fixity, fmts, S), s)) -> ( let lhs = fmtExp (G, d + 1, Ctxt (fixity, [], 0), fst (S, s)) in let rhs = fmtExp (G, d + 1, Ctxt (fixity, [], 0), snd (S, s)) in  addAccum (parens ((fixity', fixity), F.HVbox ([lhs] @ fmts @ [rhs])), fixity', accum) ) | (G, d, Ctxt (fixity', accum, l), (OpArgs (fixity, fmts, S), s)) -> ( let accMore = eqFix (fixity', fixity) in let pfx = if accMore && elide (l) then [] else if accMore && addots (l) then [ldots; F.Break] else fmts in  if accMore then fmtExp (G, d, Ctxt (fixity, accum @ pfx, l + 1), fst (S, s)) else ( let whole = fmtExp (G, d, Ctxt (fixity, pfx, 0), fst (S, s)) in  addAccum (parens ((fixity', fixity), whole), fixity', accum) ) ) | (G, d, Ctxt (fixity', accum, l), (OpArgs (fixity, fmts, S), s)) -> ( let accMore = eqFix (fixity', fixity) in let pfx = if accMore && elide (l) then [] else if accMore && addots (l) then [F.Break; ldots] else fmts in  if accMore then fmtExp (G, d, Ctxt (fixity, pfx @ accum, l + 1), fst (S, s)) else ( let whole = fmtExp (G, d, Ctxt (fixity, pfx, 0), fst (S, s)) in  addAccum (parens ((fixity', fixity), whole), fixity', accum) ) )
and braces (G, d, ((D, V), s))  = OpArgs (FX.Prefix (binderPrec), [sym "{"; fmtDec (G, d, (D, s)); sym "}"; F.Break], IntSyn.App (V, IntSyn.Nil))
and brackets (G, d, ((D, U), s))  = OpArgs (FX.Prefix (binderPrec), [sym "["; fmtDec (G, d, (D, s)); sym "]"; F.Break], IntSyn.App (U, IntSyn.Nil))
and fmtDec = function (G, d, (I.Dec (x, V), s)) -> F.HVbox [Str0 (Symbol.bvar (nameOf (x))); sym ":"; fmtExp (G, d + 1, noCtxt, (V, s))] | (G, d, (I.BDec (x, (cid, t)), s)) -> ( let (Gsome, Gblock) = I.constBlock cid in  F.HVbox ([Str0 (Symbol.const (nameOf (x))); sym ":"] @ fmtDecList' (G, (Gblock, I.comp (t, s)))) ) | (G, d, (I.ADec (x, _), s)) -> F.HVbox [Str0 (Symbol.bvar (nameOf (x))); sym ":_"] | (G, d, (I.NDec (Some name), s)) -> F.HVbox [sym name]
and fmtDecList' = function (G0, ([], s)) -> [] | (G0, (D :: [], s)) -> sym "{" :: fmtDec (G0, 0, (D, s)) :: sym "}" :: [] | (G0, (D :: L, s)) -> sym "{" :: fmtDec (G0, 0, (D, s)) :: sym "}" :: F.Break :: fmtDecList' (I.Decl (G0, D), (L, I.dot1 s))
let rec skipI = function (0, G, V) -> (G, V) | (i, G, I.Pi ((D, _), V)) -> skipI (i - 1, I.Decl (G, Names.decEName (G, D)), V)
let rec skipI2 = function (0, G, V, U) -> (G, V, U) | (i, G, I.Pi ((D, _), V), I.Lam (D', U)) -> skipI2 (i - 1, I.Decl (G, Names.decEName (G, D')), V, U)
let rec ctxToDecList = function (I.Null, L) -> L | (I.Decl (G, D), L) -> ctxToDecList (G, D :: L)
let rec fmtDecList = function (G0, []) -> [] | (G0, D :: []) -> sym "{" :: fmtDec (G0, 0, (D, I.id)) :: sym "}" :: [] | (G0, D :: L) -> sym "{" :: fmtDec (G0, 0, (D, I.id)) :: sym "}" :: F.Break :: fmtDecList (I.Decl (G0, D), L)
(* Assume unique names are already assigned in G0 and G! *)

let rec fmtCtx (G0, G)  = fmtDecList (G0, ctxToDecList (G, []))
let rec fmtBlock = function (I.Null, Lblock) -> [sym "block"; F.Break] @ (fmtDecList (I.Null, Lblock)) | (Gsome, Lblock) -> [F.HVbox ([sym "some"; F.Space] @ (fmtCtx (I.Null, Gsome))); F.Break; F.HVbox ([sym "block"; F.Space] @ (fmtDecList (Gsome, Lblock)))]
(* fmtConDec (hide, condec) = fmt
     formats a constant declaration (which must be closed and in normal form)

     This function prints the quantifiers and abstractions only if hide = false.
  *)

let rec fmtConDec = function (hide, condec) -> ( let qid = Names.conDecQid condec in let _ = Names.varReset IntSyn.Null in let (G, V) = if hide then skipI (imp, I.Null, V) else (I.Null, V) in let Vfmt = fmtExp (G, 0, noCtxt, (V, I.id)) in  F.HVbox [fmtConstPath (Symbol.const, qid); F.Space; sym ":"; F.Break; Vfmt; sym "."] ) | (hide, condec) -> ( let qid = Names.conDecQid condec in let _ = Names.varReset IntSyn.Null in let (G, V) = if hide then skipI (imp, I.Null, V) else (I.Null, V) in let Vfmt = fmtExp (G, 0, noCtxt, (V, I.id)) in  F.HVbox [sym "%skolem"; F.Break; fmtConstPath (Symbol.skonst, qid); F.Space; sym ":"; F.Break; Vfmt; sym "."] ) | (hide, condec) -> ( let qid = Names.conDecQid condec in let _ = Names.varReset IntSyn.Null in  F.HVbox ([sym "%block"; F.Break; fmtConstPath (Symbol.label, qid); F.Space; sym ":"; F.Break] @ (fmtBlock (Gsome, Lblock)) @ [sym "."]) ) | (hide, condec) -> ( let qid = Names.conDecQid condec in let _ = Names.varReset IntSyn.Null in  F.HVbox ([sym "%block"; F.Break; fmtConstPath (Symbol.label, qid); F.Space; sym "="; F.Break] @ (formatWorlds (T.Worlds W) :: [sym "."])) ) | (hide, condec) -> ( (* val _ = Names.varReset () *)
let qid = Names.conDecQid condec in let _ = Names.varReset IntSyn.Null in let (G, V, U) = if hide then skipI2 (imp, I.Null, V, U) else (I.Null, V, U) in let Vfmt = fmtExp (G, 0, noCtxt, (V, I.id)) in let Ufmt = fmtExp (G, 0, noCtxt, (U, I.id)) in  F.HVbox [fmtConstPath (Symbol.def, qid); F.Space; sym ":"; F.Break; Vfmt; F.Break; sym "="; F.Space; Ufmt; sym "."](* removed, when abbreviations where introduced. -- cs Mon Jun  7 16:03:30 EDT 1999
        F.Vbox0 0 1 [F.HVbox [Str0 (Symbol.def (name)), F.Space, sym ":", F.Break,
                         Vfmt, F.Break,
                         sym "=", F.Space,
                         Ufmt, sym "."],
                F.Break,
                F.HVbox [sym "%strict ", Str0 (Symbol.def (name)), sym "."]]
*)
 ) | (hide, condec) -> ( (* val _ = Names.varReset () *)
let qid = Names.conDecQid condec in let _ = Names.varReset IntSyn.Null in let (G, V, U) = if hide then skipI2 (imp, I.Null, V, U) else (I.Null, V, U) in let Vfmt = fmtExp (G, 0, noCtxt, (V, I.id)) in let Ufmt = fmtExp (G, 0, noCtxt, (U, I.id)) in  F.HVbox [fmtConstPath (Symbol.def, qid); F.Space; sym ":"; F.Break; Vfmt; F.Break; sym "="; F.Space; Ufmt; sym "."](* removed, when abbreviations where introduced. -- cs Mon Jun  7 16:03:30 EDT 1999
        F.Vbox0 0 1 [F.HVbox [Str0 (Symbol.def (name)), F.Space, sym ":", F.Break,
                         Vfmt, F.Break,
                         sym "=", F.Space,
                         Ufmt, sym "."],
                F.Break,
                F.HVbox [sym "%nonstrict ", Str0 (Symbol.def (name)), sym "."]]
*)
 )
let rec fmtCnstr = function (I.Solved) -> [Str "Solved Constraint"] | (I.Eqn (G, U1, U2)) -> ( let G' = Names.ctxLUName G in  [F.HVbox [fmtExp (G', 0, noCtxt, (U1, I.id)); F.Break; sym "="; F.Space; fmtExp (G', 0, noCtxt, (U2, I.id))]] ) | (I.FgnCnstr (csfc)) -> ( let rec fmtExpL = function ([]) -> [Str "Empty Constraint"] | ((G, U) :: []) -> [fmtExp (Names.ctxLUName G, 0, noCtxt, (U, I.id))] | ((G, U) :: expL) -> [fmtExp (Names.ctxLUName G, 0, noCtxt, (U, I.id)); Str ";"; F.Break] @ fmtExpL expL in  fmtExpL (I.FgnCnstrStd.ToInternal.apply csfc ()) )
let rec fmtCnstrL = function ([]) -> [Str "Empty Constraint"] | ({ contents = Cnstr :: [] }) -> (fmtCnstr Cnstr) @ [Str "."] | ({ contents = Cnstr :: cnstrL }) -> (fmtCnstr Cnstr) @ [Str ";"; F.Break] @ (fmtCnstrL cnstrL)
(* fmtNamedEVar, fmtEVarInst and evarInstToString are used to print
     instantiations of EVars occurring in queries.  To that end, a list of
     EVars paired with their is passed, thereby representing a substitution
     for_sml logic variables.

     We always raise AVars to the empty context.
  *)

let rec abstractLam = function (I.Null, U) -> U | (I.Decl (G, D), U) -> abstractLam (G, I.Lam (D, U))
let rec fmtNamedEVar = function (U, name) -> ( let U' = abstractLam (G, U) in  F.HVbox [Str0 (Symbol.evar (name)); F.Space; sym "="; F.Break; fmtExp (I.Null, 0, noCtxt, (U', I.id))] ) | (U, name) -> F.HVbox [Str0 (Symbol.evar (name)); F.Space; sym "="; F.Break; fmtExp (I.Null, 0, noCtxt, (U, I.id))]
let rec fmtEVarInst = function ([]) -> [Str "Empty Substitution"] | ((U, name) :: []) -> [fmtNamedEVar (U, name)] | ((U, name) :: Xs) -> fmtNamedEVar (U, name) :: Str ";" :: F.Break :: fmtEVarInst Xs
(* collectEVars and collectConstraints are used to print constraints
     associated with EVars in a instantiation of variables occurring in queries.
  *)

let rec collectEVars = function ([], Xs) -> Xs | ((U, _) :: Xnames, Xs) -> collectEVars (Xnames, Abstract.collectEVars (I.Null, (U, I.id), Xs))
let rec eqCnstr r1 r2  = (r1 = r2)
let rec mergeConstraints = function ([], cnstrs2) -> cnstrs2 | (cnstr :: cnstrs1, cnstrs2) -> if List.exists (eqCnstr cnstr) cnstrs2 then mergeConstraints (cnstrs1, cnstrs2) else cnstr :: (mergeConstraints (cnstrs1, cnstrs2))
let rec collectConstraints = function ([]) -> [] | (I.EVar ({ contents = (None) }, _, _, cnstrs) :: Xs) -> mergeConstraints (Constraints.simplify (! cnstrs), collectConstraints Xs) | (_ :: Xs) -> collectConstraints (Xs)
(* In the functions below, G must be a "printing context", that is,
     (a) unique names must be assigned to each declaration which may
         actually applied in the scope (typically, using Names.decName)
     (b) types need not be well-formed, since they are not used
  *)

let rec formatDec (G, D)  = fmtDec (G, 0, (D, I.id))
let rec formatDecList (G, D)  = F.HVbox (fmtDecList (G, D))
let rec formatDecList' (G, (D, s))  = F.HVbox (fmtDecList' (G, (D, s)))
let rec formatExp (G, U)  = fmtExp (G, 0, noCtxt, (U, I.id))
let rec formatSpine (G, S)  = fmtSpine (G, 0, 0, (S, I.id))
let rec formatConDec (condec)  = fmtConDec (false, condec)
let rec formatConDecI (condec)  = fmtConDec (true, condec)
let rec formatCnstr (Cnstr)  = F.Vbox0 0 1 (fmtCnstr Cnstr)
let rec formatCnstrs (cnstrL)  = F.Vbox0 0 1 (fmtCnstrL cnstrL)
let rec formatCtx (G0, G)  = F.HVbox (fmtCtx (G0, G))
(* assumes G0 and G are named *)

let rec decToString (G, D)  = F.makestring_fmt (formatDec (G, D))
let rec expToString (G, U)  = F.makestring_fmt (formatExp (G, U))
let rec conDecToString (condec)  = F.makestring_fmt (formatConDec (condec))
let rec cnstrToString (Cnstr)  = F.makestring_fmt (formatCnstr Cnstr)
let rec cnstrsToString (cnstrL)  = F.makestring_fmt (formatCnstrs cnstrL)
let rec ctxToString (G0, G)  = F.makestring_fmt (formatCtx (G0, G))
let rec evarInstToString Xnames  = F.makestring_fmt (F.Hbox [F.Vbox0 0 1 (fmtEVarInst Xnames); Str "."])
let rec evarCnstrsToStringOpt Xnames  = ( (* collect EVars in instantiations *)
let Ys = collectEVars (Xnames, []) in let cnstrL = collectConstraints Ys in  match cnstrL with [] -> None | _ -> Some (cnstrsToString (cnstrL)) )
let rec printSgn ()  = IntSyn.sgnApp (fun (cid) -> (print (F.makestring_fmt (formatConDecI (IntSyn.sgnLookup cid))); print "\n"))
let formatWorlds = formatWorlds
let worldsToString = worldsToString
(* local ... *)

 end

(* functor Print *)

