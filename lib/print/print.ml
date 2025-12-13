(* Printing *)
(* Author: Frank Pfenning *)
(* Modified: Jeff Polakow, Roberto Virga *)

functor (* GEN BEGIN FUNCTOR DECL *) Print ((*! structure IntSyn' : INTSYN !*)
               structure Whnf : WHNF
               (*! sharing Whnf.IntSyn = IntSyn' !*)
               structure Abstract : ABSTRACT
               (*! sharing Abstract.IntSyn = IntSyn' !*)
               structure Constraints : CONSTRAINTS
               (*! sharing Constraints.IntSyn = IntSyn' !*)
               structure Names : NAMES
               (*! sharing Names.IntSyn = IntSyn' !*)
               structure Formatter' : FORMATTER
               structure Symbol : SYMBOL)
  : PRINT =
struct

  (*! structure IntSyn = IntSyn' !*)
structure Formatter = Formatter'
 structure Tomega = Tomega

(* Externally visible parameters *)

(* GEN BEGIN TAG OUTSIDE LET *) val implicit = ref (false) (* GEN END TAG OUTSIDE LET *)              (* whether to print implicit arguments *)
(* GEN BEGIN TAG OUTSIDE LET *) val printInfix = ref (false) (* GEN END TAG OUTSIDE LET *)            (* if implicit is ref true, whether to print infix ops when possible *)
(* GEN BEGIN TAG OUTSIDE LET *) val printDepth = ref (NONE:int option) (* GEN END TAG OUTSIDE LET *)  (* limit on term depth to print *)
(* GEN BEGIN TAG OUTSIDE LET *) val printLength = ref (NONE:int option) (* GEN END TAG OUTSIDE LET *) (* limit on number of arguments to print *)
(* GEN BEGIN TAG OUTSIDE LET *) val noShadow = ref (false) (* GEN END TAG OUTSIDE LET *)              (* if true, don't print shadowed constants as "%const%" *)

local

  (* Shorthands *)
  structure I = IntSyn
  structure FX = Names.Fixity
  structure F = Formatter
  structure T = Tomega

  (* Disambiguation of block logic variable names *)
  (* GEN BEGIN TAG OUTSIDE LET *) val lvars : I.block option ref list ref
            = ref nil (* GEN END TAG OUTSIDE LET *)
  fun lookuplvar (l) =
      let
        (* GEN BEGIN TAG OUTSIDE LET *) val _ = if (List.exists ((* GEN BEGIN FUNCTION EXPRESSION *) fn r => r = l (* GEN END FUNCTION EXPRESSION *)) (!lvars)) then () else lvars := !lvars @ [l] (* GEN END TAG OUTSIDE LET *)   (* speed improvment possible Tue Mar  1 13:27:04 2011 --cs *)
        fun find (r :: L) n =  if r = l then n else find L (n+1)
      in
        Int.toString (find (!lvars) 0)
      end


  (* GEN BEGIN TAG OUTSIDE LET *) val Str = F.String (* GEN END TAG OUTSIDE LET *)
  fun Str0 (s, n) = F.String0 n s
  fun sym (s) = Str0 (Symbol.sym s)

  fun (* GEN BEGIN FUN FIRST *) nameOf (SOME(id)) = id (* GEN END FUN FIRST *)
    | (* GEN BEGIN FUN BRANCH *) nameOf (NONE) = "_" (* GEN END FUN BRANCH *)

  (* fmtEVar (G, X) = "X", the name of the EVar X *)
  (* Effect: Names.evarName will assign a name if X does not yet have one *)
  fun fmtEVar (G, X) = Str0 (Symbol.evar (Names.evarName(G, X)))
  (* should probably be a new Symbol constructor for AVars -kw *)
  fun fmtAVar (G, X) = Str0 (Symbol.evar (Names.evarName(G, X) ^ "_"))

  (* isNil S = true iff S == Nil *)
  fun (* GEN BEGIN FUN FIRST *) isNil (I.Nil) = true (* GEN END FUN FIRST *)
    | (* GEN BEGIN FUN BRANCH *) isNil (I.App _) = false (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) isNil (I.SClo(S,_)) = isNil S (* GEN END FUN BRANCH *)

  (* subToSpine (depth, s) = S
     Invariants:
     If  G |- s : G', Gd  with  |Gd| = depth
     then G |- S : {{Gd}} C > C  for any C

     This is used to print
      G |- Xl[s] : A[s]  for  G', Gd |- Xl : A
     as
      G |- Xr @ S : A[s]  for  G' |- Xr : {{Gd}} A
     where Xr is the raised version of Xl.
     Xr is not actually created, just printed using the name of Xl.
  *)
  fun subToSpine (depth, s) =
      let fun (* GEN BEGIN FUN FIRST *) sTS (I.Shift(k), S) =
              if k < depth
                then sTS (I.Dot (I.Idx (k+1), I.Shift(k+1)), S)
              else (* k >= depth *) S (* GEN END FUN FIRST *)
            | (* GEN BEGIN FUN BRANCH *) sTS (I.Dot(I.Idx(k), s), S) =
                (* Eta violation, but probably inconsequential -kw *)
                sTS (s, I.App(I.Root(I.BVar(k), I.Nil), S)) (* GEN END FUN BRANCH *)
            | (* GEN BEGIN FUN BRANCH *) sTS (I.Dot(I.Exp(U), s), S) =
                sTS (s, I.App(U, S)) (* GEN END FUN BRANCH *)
      in
        sTS (s, I.Nil)
      end

  (* ArgStatus classifies the number of arguments to an operator *)
  datatype arg_status =
      TooFew
    | Exact of I.spine
    | TooMany of I.spine * I.spine

  fun (* GEN BEGIN FUN FIRST *) sclo' (TooFew, s) = TooFew (* GEN END FUN FIRST *)
    | (* GEN BEGIN FUN BRANCH *) sclo' (Exact(S), s) = Exact (I.SClo(S,s)) (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) sclo' (TooMany (S, S'), s) = TooMany (I.SClo (S, s), I.SClo (S', s)) (* GEN END FUN BRANCH *)

  fun (* GEN BEGIN FUN FIRST *) sclo'' (TooFew, s) = TooFew (* GEN END FUN FIRST *)
    | (* GEN BEGIN FUN BRANCH *) sclo'' (Exact(S), s) = Exact (S) (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) sclo'' (TooMany (S, S'), s) = TooMany (S, I.SClo (S', s)) (* GEN END FUN BRANCH *)

  (* dropImp (i, S, n) for n >= 1
     = TooFew            if |S| < i+n
     = Exact(S')         if n >= 1, |S| = i+n, S = _ @ S' and |S'| = n
                         if n = 0, |S| = _ @ S', |_| = i
     = TooMany(S', S'')  if n >=1, |S| > i+n, S = _ @ S' and |S'| > n,
                                              S' = S0 @ S'' and |S0| = n
  *)
  fun (* GEN BEGIN FUN FIRST *) dropImp (0, S, 0) = Exact(S) (* GEN END FUN FIRST *)
    | (* GEN BEGIN FUN BRANCH *) dropImp (0, S, n) = (* n >= 1 *)
      let fun (* GEN BEGIN FUN FIRST *) checkArgNumber (I.Nil, 0) = Exact(S) (* GEN END FUN FIRST *)
            | (* GEN BEGIN FUN BRANCH *) checkArgNumber (I.Nil, k) = TooFew (* GEN END FUN BRANCH *)
            | (* GEN BEGIN FUN BRANCH *) checkArgNumber (S' as I.App _, 0) = TooMany (S, S') (* GEN END FUN BRANCH *)
            | (* GEN BEGIN FUN BRANCH *) checkArgNumber (I.App(U,S'), k) = checkArgNumber (S', k-1) (* GEN END FUN BRANCH *)
            | (* GEN BEGIN FUN BRANCH *) checkArgNumber (I.SClo(S', s), k) = sclo'' (checkArgNumber (S', k), s) (* GEN END FUN BRANCH *)
      in
        checkArgNumber (S, n)
      end (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) dropImp (i, I.App(U,S), n) = dropImp (i-1, S, n) (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) dropImp (i, I.SClo(S,s), n) =
        sclo' (dropImp (i, S, n), s) (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) dropImp (i, I.Nil, n) = TooFew (* GEN END FUN BRANCH *)

  (* exceeded (n:int, b:bound) = true if n exceeds bound b *)
  fun (* GEN BEGIN FUN FIRST *) exceeded (_,NONE) = false (* GEN END FUN FIRST *)
    | (* GEN BEGIN FUN BRANCH *) exceeded (n:int,SOME(m:int)) = n >= m (* GEN END FUN BRANCH *)

  (* Type ctxt is the "left context" of an expression to be printed.
     It works as an accumulator and is used to decide whether to insert of parentheses
     or elide nested subexpressions.

     Ctxt (fixity, formats, length)
     is the "left context" of an expression to be printed.  When printed
     it will be the string prefixed to the string representing the
     current expression.

     fixity is the operator and precedence in effect,
     formats is the list of formats which make up the left context
     length is the length of the left context (used for printLength elision)
  *)
  datatype ctxt = Ctxt of FX.fixity * F.format list * int

  (* Type opargs represent the operator/arguments form of roots.

     OpArgs (fixity, formats, S)
     represents the printed form of a root expression H @ S:
      fixity is the fixity of H (possibly FX.Nonfix),
      formats is a list of formats for printing H (including surrounding breaks
         and whitespace),
      S is the spine of arguments.
      There may be additional argument in S which are ignored.

     EtaLong (U)
     represents an expression U' which had to be eta-expanded to U
     in order to supply enough arguments to a prefix, postfix, or infix operator
     so it can be printed.
  *)
  datatype opargs =
      OpArgs of FX.fixity * F.format list * I.spine
    | EtaLong of I.exp

  (* GEN BEGIN TAG OUTSIDE LET *) val noCtxt = Ctxt (FX.Prefix(FX.dec (FX.dec (FX.dec (FX.dec FX.minPrec)))), [], 0) (* GEN END TAG OUTSIDE LET *)
                                        (* empty left context *)

  (* GEN BEGIN TAG OUTSIDE LET *) val binderPrec = FX.dec (FX.dec (FX.dec FX.minPrec)) (* GEN END TAG OUTSIDE LET *)
                                        (* braces and brackets as a prefix operator *)
  (* colon is of FX.minPrec-2, but doesn't occur in printing *)
  (* GEN BEGIN TAG OUTSIDE LET *) val arrowPrec = FX.dec FX.minPrec (* GEN END TAG OUTSIDE LET *)     (* arrow as infix operator *)
  (* GEN BEGIN TAG OUTSIDE LET *) val juxPrec = FX.inc FX.maxPrec (* GEN END TAG OUTSIDE LET *)       (* juxtaposition as infix operator *)

  (* arrow (V1, V2) = oa
     where oa is the operator/argument representation of V1 -> V2
  *)
  fun arrow (V1, V2) =
         OpArgs(FX.Infix(arrowPrec, FX.Right),
                [F.Break, sym "->", F.Space],
                I.App (V1, I.App(V2, I.Nil)))

  (* Nonfix corresponds to application and therefore has precedence juxPrex (which is maximal) *)
  (* GEN BEGIN TAG OUTSIDE LET *) val appCtxt = Ctxt (FX.Nonfix, [], 0) (* GEN END TAG OUTSIDE LET *)

  (* fixityCon (c) = fixity of c *)
  fun (* GEN BEGIN FUN FIRST *) fixityCon (I.Const(cid)) = Names.getFixity (cid) (* GEN END FUN FIRST *)
    | (* GEN BEGIN FUN BRANCH *) fixityCon (I.Skonst(cid)) = FX.Nonfix (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) fixityCon (I.Def(cid)) = Names.getFixity (cid) (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) fixityCon (I.NSDef(cid)) = Names.getFixity (cid) (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) fixityCon _ = FX.Nonfix (* GEN END FUN BRANCH *) (* BVar, FVar *)

  (* impCon (c) = number of implicit arguments to c *)
  fun (* GEN BEGIN FUN FIRST *) impCon (I.Const(cid)) = I.constImp (cid) (* GEN END FUN FIRST *)
    | (* GEN BEGIN FUN BRANCH *) impCon (I.Skonst(cid)) = I.constImp (cid) (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) impCon (I.Def(cid)) = I.constImp (cid) (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) impCon (I.NSDef(cid)) = I.constImp (cid) (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) impCon _ = 0 (* GEN END FUN BRANCH *)                      (* BVar, FVar *)

  (* argNumber (fixity) = number of required arguments to head with fixity *)
  fun (* GEN BEGIN FUN FIRST *) argNumber (FX.Nonfix) = 0 (* GEN END FUN FIRST *)
    | (* GEN BEGIN FUN BRANCH *) argNumber (FX.Infix _) = 2 (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) argNumber (FX.Prefix _) = 1 (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) argNumber (FX.Postfix _) = 1 (* GEN END FUN BRANCH *)

  (* FIX: this is certainly not correct -kw *)
  fun fmtConstPath (f, Names.Qid (ids, id)) =
        F.HVbox (foldr ((* GEN BEGIN FUNCTION EXPRESSION *) fn (id, fmt) => Str0 (Symbol.str (id))::sym "."::fmt (* GEN END FUNCTION EXPRESSION *))
                       [Str0 (f (id))] ids)

  fun (* GEN BEGIN FUN FIRST *) parmDec (D::L, 1) = D (* GEN END FUN FIRST *)
    | (* GEN BEGIN FUN BRANCH *) parmDec (D::L, j) = parmDec (L, j-1) (* GEN END FUN BRANCH *)

  fun parmName (cid, i) =
      let
        (* GEN BEGIN TAG OUTSIDE LET *) val (Gsome, Gblock) = I.constBlock (cid) (* GEN END TAG OUTSIDE LET *)
      in
        case parmDec (Gblock, i)
          of I.Dec (SOME(pname), _) => pname
           | I.Dec (NONE, _) => Int.toString i
      end

  fun (* GEN BEGIN FUN FIRST *) projName (G, I.Proj (I.Bidx(k), i)) =
      let
        (* GEN BEGIN TAG OUTSIDE LET *) val I.BDec (SOME(bname), (cid, t)) = I.ctxLookup (G, k) (* GEN END TAG OUTSIDE LET *)
        (* names should have been assigned by invar
         iant, NONE imppossible *)
       in
         bname ^ "_" ^ parmName (cid, i)
       end (* GEN END FUN FIRST *)
    | (* GEN BEGIN FUN BRANCH *) projName (G, I.Proj (I.LVar(r, _, (cid, t)), i)) =
      (* note: this obscures LVar identity! *)
      (* no longer Tue Mar  1 13:32:21 2011 -cs *)
         "_"  ^ parmName (cid, i) (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) projName (G, I.Proj (I.Inst iota, i)) =
       "*" (* GEN END FUN BRANCH *)    (* to be fixed --cs *)


  fun constQid (cid) =
      if !noShadow
      then Names.conDecQid (I.sgnLookup cid)
      else Names.constQid cid

    fun cidToFmt (cid) = F.String (Names.qidToString (Names.constQid cid))
    fun (* GEN BEGIN FUN FIRST *) formatCids (nil) = nil (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) formatCids (cid::nil) = [cidToFmt cid] (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) formatCids (cid::cids) = cidToFmt cid
                                 :: F.Break :: F.String "|" :: F.Space
                                 :: formatCids cids (* GEN END FUN BRANCH *)

    fun formatWorlds (T.Worlds cids) =
        F.Hbox [F.String "(", F.HVbox (formatCids cids), F.String ")"]


    fun worldsToString (W) = F.makestring_fmt (formatWorlds W)

  (* fmtCon (c) = "c" where the name is assigned according the the Name table
     maintained in the names module.
     FVar's are printed with a preceding "`" (backquote) character
  *)
  fun (* GEN BEGIN FUN FIRST *) fmtCon (G, I.BVar(n)) = Str0 (Symbol.bvar (Names.bvarName(G, n))) (* GEN END FUN FIRST *)
    | (* GEN BEGIN FUN BRANCH *) fmtCon (G, I.Const(cid)) = fmtConstPath (Symbol.const, constQid (cid)) (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) fmtCon (G, I.Skonst(cid)) = fmtConstPath (Symbol.skonst, constQid (cid)) (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) fmtCon (G, I.Def(cid)) = fmtConstPath (Symbol.def, constQid (cid)) (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) fmtCon (G, I.NSDef (cid)) = fmtConstPath (Symbol.def, constQid (cid)) (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) fmtCon (G, I.FVar (name, _, _)) = Str0 (Symbol.fvar (name)) (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) fmtCon (G, H as I.Proj (I.Bidx(k), i)) =
        Str0 (Symbol.const (projName (G, H))) (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) fmtCon (G, H as I.Proj (I.LVar(r as ref NONE, sk, (cid, t)), i)) =
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val n = lookuplvar (r) (* GEN END TAG OUTSIDE LET *)
        in
          (* LVar fixed Sun Dec  1 11:36:55 2002 -cs *)
          fmtConstPath ((* GEN BEGIN FUNCTION EXPRESSION *) fn l0 => Symbol.const ("#[" ^ l0 ^ n ^ "]" ^ projName (G, H)) (* GEN END FUNCTION EXPRESSION *),
                        constQid (cid))
        end (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) fmtCon (G, I.FgnConst (cs, conDec)) =
        let
          (* will need to be changed if qualified constraint constant
             names are introduced... anyway, why should the user be
             allowed to shadow constraint constants? -kw *)
          (* GEN BEGIN TAG OUTSIDE LET *) val name = I.conDecName conDec (* GEN END TAG OUTSIDE LET *)
        in
          case (Names.constLookup (Names.Qid (nil, name)), !noShadow)
            of (SOME _, false) => (* the user has re-defined this name *)
                 Str0 (Symbol.const ("%" ^ name ^ "%"))
             | _ =>
                 Str0 (Symbol.const name)
        end (* GEN END FUN BRANCH *)

    (* evarArgs (G, d, X, s)
     formats X[s] by printing X @ S, where S is the substitution s in spine form.
     This is an implicit form of raising.
  *)
  fun evarArgs (G, d, X, s) =
      OpArgs (FX.Nonfix, [fmtEVar(G, X)],
              subToSpine (I.ctxLength(G), s))


  fun evarArgs' (G, d, X, s) =
      OpArgs (FX.Nonfix, [fmtAVar(G, X)],
              subToSpine (I.ctxLength(G), s))

  (* fst (S, s) = U1, the first argument in S[s] *)
  fun (* GEN BEGIN FUN FIRST *) fst (I.App (U1, _), s) = (U1, s) (* GEN END FUN FIRST *)
    | (* GEN BEGIN FUN BRANCH *) fst (I.SClo (S, s'), s) = fst (S, I.comp (s', s)) (* GEN END FUN BRANCH *)

  (* snd (S, s) = U2, the second argument in S[s] *)
  fun (* GEN BEGIN FUN FIRST *) snd (I.App (U1, S), s) = fst (S, s) (* GEN END FUN FIRST *)
    | (* GEN BEGIN FUN BRANCH *) snd (I.SClo (S, s'), s) = snd (S, I.comp (s', s)) (* GEN END FUN BRANCH *)

  (* elide (l) = true  iff  l exceeds the optional printLength bound *)
  fun elide (l) = case !printLength
                     of NONE => false
                      | SOME(l') => (l > l')

  (* GEN BEGIN TAG OUTSIDE LET *) val ldots = sym "..." (* GEN END TAG OUTSIDE LET *)

  (* addots (l) = true  iff  l is equal to the optional printLength bound *)
  fun addots (l) = case !printLength
                     of NONE => false
                      | SOME(l') => (l = l')

  (* parens ((fixity', fixity), fmt) = fmt'
     where fmt' contains additional parentheses when the precedence of
     fixity' is greater or equal to that of fixity, otherwise it is unchanged.
  *)
  fun parens ((fixity', fixity), fmt) =
      if FX.leq (FX.prec(fixity), FX.prec(fixity'))
        then F.Hbox [sym "(", fmt, sym ")"]
      else fmt

  (* eqFix (fixity, fixity') = true iff fixity and fixity' have the same precedence
     Invariant: only called when precedence comparison is necessary to resolve
                the question if parentheses should be added
  *)
  fun (* GEN BEGIN FUN FIRST *) eqFix (FX.Infix(p,FX.Left), FX.Infix(p',FX.Left)) = (p = p') (* GEN END FUN FIRST *)
    | (* GEN BEGIN FUN BRANCH *) eqFix (FX.Infix(p,FX.Right), FX.Infix(p', FX.Right)) = (p = p') (* GEN END FUN BRANCH *)
      (* Infix(_,None) should never be asked *)
    | (* GEN BEGIN FUN BRANCH *) eqFix (FX.Prefix(p), FX.Prefix(p')) = (p = p') (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) eqFix (FX.Postfix(p), FX.Postfix(p')) = (p = p') (* GEN END FUN BRANCH *)
      (* Nonfix should never be asked *)
    | (* GEN BEGIN FUN BRANCH *) eqFix _ = false (* GEN END FUN BRANCH *)

  (* addAccum (fmt, fixity, accum) = fmt'
     Extend the current "left context" with operator fixity
     and format list accum by fmt.

     This is not very efficient, since the accumulator is copied
     for right associative or prefix operators.
  *)
  fun (* GEN BEGIN FUN FIRST *) addAccum (fmt, _, nil) = fmt (* GEN END FUN FIRST *)
    | (* GEN BEGIN FUN BRANCH *) addAccum (fmt, FX.Infix(_, FX.Left), accum) = F.HVbox ([fmt] @ accum) (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) addAccum (fmt, FX.Infix(_, FX.Right), accum) = F.HVbox (accum @ [fmt]) (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) addAccum (fmt, FX.Prefix _, accum) = F.HVbox (accum @ [fmt]) (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) addAccum (fmt, FX.Postfix _, accum) = F.HVbox ([fmt] @ accum) (* GEN END FUN BRANCH *)
    (* FX.Infix(None,_), FX.Nonfix should never arise *)

  (* aa (ctx, fmt) = fmt'
     Extend the current "left context" by fmt.
  *)
  fun aa (Ctxt (fixity, accum, l), fmt) = addAccum (fmt, fixity, accum)

  (* fmtUni (L) = "L" *)
  fun (* GEN BEGIN FUN FIRST *) fmtUni (I.Type) = sym "type" (* GEN END FUN FIRST *)
    | (* GEN BEGIN FUN BRANCH *) fmtUni (I.Kind) = sym "kind" (* GEN END FUN BRANCH *)   (* impossible, included for robustness *)

  (* fmtExpW (G, d, ctx, (U, s)) = fmt

     format the expression U[s] at printing depth d and add it to the left context
     ctx.

     Invariants:
       G is a "printing context" (names in it are unique, but
            types may be incorrect) approximating G'
       G'' |- U : V   G' |- s : G''  (so  G' |- U[s] : V[s])
       (U,s) in whnf
  *)
  fun (* GEN BEGIN FUN FIRST *) fmtExpW (G, d, ctx, (I.Uni(L), s)) = aa (ctx, fmtUni(L)) (* GEN END FUN FIRST *)
    | (* GEN BEGIN FUN BRANCH *) fmtExpW (G, d, ctx, (I.Pi((D as I.Dec(_,V1),P),V2), s)) =
      (case P (* if Pi is dependent but anonymous, invent name here *)
         of I.Maybe => let
                         (* GEN BEGIN TAG OUTSIDE LET *) val D' = Names.decLUName (G, D) (* GEN END TAG OUTSIDE LET *) (* could sometimes be EName *)
                       in
                         fmtLevel (I.Decl (G, D'), (* I.decSub (D', s) *)
                                   d, ctx, (braces (G, d, ((D',V2), s)),
                                            I.dot1 s))
                       end
          | I.Meta => let
                         (* GEN BEGIN TAG OUTSIDE LET *) val D' = Names.decLUName (G, D) (* GEN END TAG OUTSIDE LET *)
                       in
                         fmtLevel (I.Decl (G, D'), (* I.decSub (D', s) *)
                                   d, ctx, (braces (G, d, ((D',V2), s)),
                                            I.dot1 s))
                       end
          | I.No => fmtLevel (I.Decl (G, D), (* I.decSub (D, s) *)
                              d, ctx, (arrow(I.EClo(V1,I.shift), V2), I.dot1 s))) (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) fmtExpW (G, d, ctx, (I.Pi((D as I.BDec _, P), V2), s)) =
      let
        (* GEN BEGIN TAG OUTSIDE LET *) val D' = Names.decLUName (G, D) (* GEN END TAG OUTSIDE LET *)
      in
         fmtLevel (I.Decl (G, D'), d, ctx, (braces (G, d, ((D', V2), s)),
                                            I.dot1 s))
      end (* GEN END FUN BRANCH *)
    (* -bp *)
    | (* GEN BEGIN FUN BRANCH *) fmtExpW (G, d, ctx, (I.Pi((D as I.ADec _, P), V2), s)) =
      let
    (*      val D' = Names.decLUName (G, D) *)
        (* GEN BEGIN TAG OUTSIDE LET *) val braces = OpArgs(FX.Prefix(binderPrec),
                            [sym "[" , sym "_", sym "]", F.Break],
                IntSyn.App(V2, IntSyn.Nil)) (* GEN END TAG OUTSIDE LET *)
      in
         fmtLevel (I.Decl (G, D), d, ctx, (braces, I.dot1 s))
      end (* GEN END FUN BRANCH *)

    | (* GEN BEGIN FUN BRANCH *) fmtExpW (G, d, ctx, (U as I.Root R, s)) = (* s = id *)
         fmtOpArgs (G, d, ctx, opargs (G, d, R), s) (* GEN END FUN BRANCH *)
    (* I.Redex not possible *)
    | (* GEN BEGIN FUN BRANCH *) fmtExpW (G, d, ctx, (I.Lam(D, U), s)) =
      let
        (* GEN BEGIN TAG OUTSIDE LET *) val D' = Names.decLUName (G, D) (* GEN END TAG OUTSIDE LET *)
      in
        fmtLevel (I.Decl (G, D'), (* I.decSub (D', s) *)
                  d, ctx, (brackets (G, d, ((D', U), s)), I.dot1 s))
      end (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) fmtExpW (G, d, ctx, (X as I.EVar _, s)) =
      (* assume dereferenced during whnf *)
      if !implicit then aa (ctx, F.HVbox (fmtEVar(G,X)::fmtSub(G,d,s)))
      else fmtOpArgs (G, d, ctx, evarArgs (G, d, X, s), I.id) (* GEN END FUN BRANCH *)

    | (* GEN BEGIN FUN BRANCH *) fmtExpW (G, d, ctx, (X as I.AVar _, s)) =
      (* assume dereferenced during whnf *)
      if !implicit then aa (ctx, F.HVbox (fmtAVar(G,X)::fmtSub(G,d,s)))
      else fmtOpArgs (G, d, ctx, evarArgs' (G, d, X, s), I.id) (* GEN END FUN BRANCH *)

    | (* GEN BEGIN FUN BRANCH *) fmtExpW (G, d, ctx, (U as I.FgnExp csfe, s)) =
      fmtExp (G, d, ctx, (I.FgnExpStd.ToInternal.apply csfe (), s)) (* GEN END FUN BRANCH *)
    (* I.EClo not possible for Whnf *)

  (* for internal printing *)
  (* opargsImplicit (G, (C, S)) = oa
     converts C @ S into operator/arguments form, showing all implicit
     arguments.  In this form, infix, prefix, and postfix declarations
     are ignored.
  *)
  and opargsImplicit (G, d, (C,S)) = OpArgs (FX.Nonfix, [fmtCon(G,C)], S)

  (* for flit printing -jcreed 6/2005 *)
  (* opargsImplicit (G, (C, S)) = oa
     converts C @ S into operator/arguments form, showing all implicit
     arguments.  In this form, infix declarations are obeyed. It is an
     error to call this function if an infix declaration has been made for
     a term which has more than two arguments. (This could have happened if the term
     had two explicit arguments and further implicit arguments)

     In other words, it is an error if an infix declaration had any
     implicit arguments.
  *)
  and opargsImplicitInfix (G, d, R as (C,S)) =
      let
          (* GEN BEGIN TAG OUTSIDE LET *) val fixity = fixityCon C (* GEN END TAG OUTSIDE LET *)
      in
          case fixity of
              FX.Infix _ => opargsExplicit(G, d, R) (* Can't have implicit arguments by invariant *)
            | _          => OpArgs (FX.Nonfix, [fmtCon (G, C)], S)
      end

  (* for external printing *)
  (* opargsExplicit (G, (C, S)) = oa
     converts C @ S into operator/arguments form, eliding implicit
     arguments and taking operator fixity declarations into account.
     G |- C @ S (no substitution involved)
  *)
  and opargsExplicit (G, d, R as (C,S)) =
      let
        (* GEN BEGIN TAG OUTSIDE LET *) val opFmt = fmtCon (G, C) (* GEN END TAG OUTSIDE LET *)
        (* GEN BEGIN TAG OUTSIDE LET *) val fixity = fixityCon C (* GEN END TAG OUTSIDE LET *)
        fun (* GEN BEGIN FUN FIRST *) oe (Exact(S')) =
            (case fixity
               of FX.Nonfix => OpArgs (FX.Nonfix, [opFmt], S')
                | FX.Prefix _ => OpArgs (fixity, [opFmt, F.Break], S')
                | FX.Postfix _ => OpArgs (fixity, [F.Break, opFmt], S')
                | FX.Infix _ => OpArgs (fixity, [F.Break, opFmt, F.Space], S')) (* GEN END FUN FIRST *)
          | (* GEN BEGIN FUN BRANCH *) oe (TooFew) = EtaLong (Whnf.etaExpandRoot (I.Root R)) (* GEN END FUN BRANCH *)
          | (* GEN BEGIN FUN BRANCH *) oe (TooMany (S', S'')) =
            (* extra arguments to infix operator *)
            (* S' - all non-implicit arguments *)
            (* S'' - extra arguments *)
            let
              (* GEN BEGIN TAG OUTSIDE LET *) val opFmt' = fmtOpArgs (G, d, noCtxt, oe (Exact (S')), I.id) (* GEN END TAG OUTSIDE LET *)
            in
              (* parens because juxtaposition has highest precedence *)
              (*
                 could be redundant for prefix or postfix operators, but
                 include anyway to avoid misreading output
              *)
              OpArgs (FX.Nonfix, [F.Hbox [sym "(", opFmt', sym ")"]], S'')
            end (* GEN END FUN BRANCH *)
      in
        oe (dropImp (impCon C, S, argNumber fixity))
      end

  (* opargs (G, d, (C, S)) = oa
     converts C @ S to operator/arguments form, depending on the
     value of !implicit
  *)
  and opargs (G, d, R) =
      if !implicit then if !printInfix then opargsImplicitInfix (G, d, R)
                        else opargsImplicit (G, d, R)
      else opargsExplicit (G, d, R)

  (* fmtOpArgs (G, d, ctx, oa, s) = fmt
     format the operator/arguments form oa at printing depth d and add it
     to the left context ctx.

     G is a printing context approximating G', and G' |- oa[s] is valid.
  *)
  and (* GEN BEGIN FUN FIRST *) fmtOpArgs (G, d, ctx, oa as OpArgs(_, opFmts, S'), s) =
      if isNil S'
        then aa (ctx, List.hd opFmts)   (* opFmts = [fmtCon(G,C)] *)
      else fmtLevel (G, d, ctx, (oa, s)) (* GEN END FUN FIRST *)
    | (* GEN BEGIN FUN BRANCH *) fmtOpArgs (G, d, ctx, EtaLong(U'), s) =
        fmtExpW (G, d, ctx, (U', s)) (* GEN END FUN BRANCH *)

  (* fmtSub (G, d, s) = fmt
     format substitution s at printing depth d and printing context G.

     This is used only when !implicit = true, that is, when the internal
     representation is printed.  Note that a substitution is not reparsable
  *)
  and fmtSub (G, d, s) = Str "[" :: fmtSub' (G, d, 0, s)
  and fmtSub' (G, d, l, s) = if elide l then [ldots] else fmtSub'' (G, d, l, s)
  and (* GEN BEGIN FUN FIRST *) fmtSub'' (G, d, l, I.Shift(k)) = [Str ("^" ^ Int.toString k), Str "]"] (* GEN END FUN FIRST *)
    | (* GEN BEGIN FUN BRANCH *) fmtSub'' (G, d, l, I.Dot(I.Idx(k), s)) =
        Str (Names.bvarName (G, k)) :: Str "." :: F.Break :: fmtSub' (G, d, l+1, s) (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) fmtSub'' (G, d, l, I.Dot(I.Exp(U), s)) =
        fmtExp (G, d+1, noCtxt, (U, I.id))
        :: Str "." :: F.Break :: fmtSub' (G, d, l+1, s) (* GEN END FUN BRANCH *)

  (* fmtExp (G, d, ctx, (U, s)) = fmt
     format or elide U[s] at printing depth d and add to the left context ctx.

     G is a printing context approximation G' and G' |- U[s] is valid.
  *)
  and fmtExp (G, d, ctx, (U, s)) =
         if exceeded(d,!printDepth)
            then sym "%%"
            else fmtExpW (G, d, ctx, Whnf.whnf (U, s))

  (* fmtSpine (G, d, l, (S, s)) = fmts
     format spine S[s] at printing depth d, printing length l, in printing
     context G which approximates G', where G' |- S[s] is valid
  *)
  and (* GEN BEGIN FUN FIRST *) fmtSpine (G, d, l, (I.Nil, _)) = [] (* GEN END FUN FIRST *)
    | (* GEN BEGIN FUN BRANCH *) fmtSpine (G, d, l, (I.SClo (S, s'), s)) =
         fmtSpine (G, d, l, (S, I.comp(s',s))) (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) fmtSpine (G, d, l, (I.App(U, S), s)) =
         if elide (l) then []           (* necessary? *)
         else if addots (l) then [ldots]
              else fmtExp (G, d+1, appCtxt, (U, s))
                   :: fmtSpine' (G, d, l, (S, s)) (* GEN END FUN BRANCH *)

  (* fmtSpine' (G, d, l, (S, s)) = fmts
     like fmtSpine, but will add leading "Break" and increment printing length
  *)
  and (* GEN BEGIN FUN FIRST *) fmtSpine' (G, d, l, (I.Nil, _)) = [] (* GEN END FUN FIRST *)
    | (* GEN BEGIN FUN BRANCH *) fmtSpine' (G, d, l, (I.SClo (S, s'), s)) =
        fmtSpine' (G, d, l, (S, I.comp(s', s))) (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) fmtSpine' (G, d, l, (S, s)) =
        F.Break :: fmtSpine (G, d, l+1, (S, s)) (* GEN END FUN BRANCH *)

  (* fmtLevel (G, d, ctx, (oa, s)) = fmt

     format operator/arguments form oa[s] at printing depth d and add the result
     to the left context ctx.

     This is the main function flattening out infix/prefix/postfix operator
     sequences.  It compares the fixity of the operator of the current left
     context with the operator at the head of the current operator/arguments
     form and decides how to extend the accumulator and whether to insert
     parentheses.
  *)
  and (* GEN BEGIN FUN FIRST *) fmtLevel (G, d, Ctxt (fixity', accum, l),
                (OpArgs (fixity as FX.Nonfix, fmts, S), s)) =
      let
        (* GEN BEGIN TAG OUTSIDE LET *) val atm = fmtSpine (G, d, 0, (S,s)) (* GEN END TAG OUTSIDE LET *)
        (* atm must not be empty, otherwise bug below *)
      in
        (* F.HVbox doesn't work if last item of HVbox is F.Break *)
        addAccum (parens ((fixity',fixity), F.HVbox (fmts @ [F.Break] @ atm)),
                  fixity', accum)
        (* possible improvement along the following lines: *)
        (*
           if (#2 (F.Width (F.Hbox (fmts)))) < 4
           then F.Hbox [F.Hbox(fmts), F.HVbox0 1 1 1 atm]
           else ...
        *)
      end (* GEN END FUN FIRST *)

    | (* GEN BEGIN FUN BRANCH *) fmtLevel (G, d, Ctxt (fixity', accum, l),
                (OpArgs (fixity as (FX.Infix(p, FX.Left)), fmts, S), s)) =
      let (* GEN BEGIN TAG OUTSIDE LET *) val accMore = eqFix (fixity, fixity') (* GEN END TAG OUTSIDE LET *)
        (* GEN BEGIN TAG OUTSIDE LET *) val rhs = if accMore andalso elide(l) then []
                  else if accMore andalso addots(l) then fmts @ [ldots]
                       else fmts @ [fmtExp (G, d+1, Ctxt (FX.Infix(p,FX.None),nil,0),
                                            snd (S, s))] (* GEN END TAG OUTSIDE LET *)
      in
        if accMore
          then fmtExp (G, d, Ctxt (fixity, rhs @ accum, l+1), fst (S, s))
        else let
               (* GEN BEGIN TAG OUTSIDE LET *) val both = fmtExp (G, d, Ctxt (fixity, rhs, 0), fst (S, s)) (* GEN END TAG OUTSIDE LET *)
             in
               addAccum (parens ((fixity',fixity), both), fixity', accum)
             end
      end (* GEN END FUN BRANCH *)

    | (* GEN BEGIN FUN BRANCH *) fmtLevel (G, d, Ctxt (fixity', accum, l),
                (OpArgs (fixity as FX.Infix(p, FX.Right), fmts, S), s)) =
      let
          (* GEN BEGIN TAG OUTSIDE LET *) val accMore = eqFix (fixity, fixity') (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val lhs = if accMore andalso elide(l) then []
                    else if accMore andalso addots(l) then [ldots] @ fmts
                         else [fmtExp (G, d+1, Ctxt (FX.Infix(p,FX.None),nil,0), fst(S, s))] @ fmts (* GEN END TAG OUTSIDE LET *)
      in
        if accMore
          then fmtExp (G, d, Ctxt (fixity, accum @ lhs, l+1), snd (S, s))
        else let
               (* GEN BEGIN TAG OUTSIDE LET *) val both = fmtExp (G, d, Ctxt (fixity, lhs, 0), snd (S, s)) (* GEN END TAG OUTSIDE LET *)
             in
               addAccum (parens ((fixity', fixity), both), fixity', accum)
             end
      end (* GEN END FUN BRANCH *)

    | (* GEN BEGIN FUN BRANCH *) fmtLevel (G, d, Ctxt (fixity', accum, l),
                (OpArgs(fixity as (FX.Infix(_,FX.None)), fmts, S), s)) =
      let
          (* GEN BEGIN TAG OUTSIDE LET *) val lhs = fmtExp (G, d+1, Ctxt (fixity, nil, 0), fst(S, s)) (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val rhs = fmtExp (G, d+1, Ctxt (fixity, nil, 0), snd(S, s)) (* GEN END TAG OUTSIDE LET *)
      in
        addAccum (parens ((fixity',fixity),
                          F.HVbox ([lhs] @ fmts @ [rhs])), fixity', accum)
      end (* GEN END FUN BRANCH *)

    | (* GEN BEGIN FUN BRANCH *) fmtLevel (G, d, Ctxt (fixity', accum, l),
                (OpArgs (fixity as (FX.Prefix _), fmts, S), s)) =
      let
          (* GEN BEGIN TAG OUTSIDE LET *) val accMore = eqFix (fixity', fixity) (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val pfx = if accMore andalso elide(l) then []
                    else if accMore andalso addots(l) then [ldots, F.Break]
                         else fmts (* GEN END TAG OUTSIDE LET *)
      in
        if accMore
          then fmtExp (G, d, Ctxt (fixity, accum @ pfx, l+1), fst(S, s))
        else let
               (* GEN BEGIN TAG OUTSIDE LET *) val whole = fmtExp (G, d, Ctxt (fixity, pfx, 0), fst (S, s)) (* GEN END TAG OUTSIDE LET *)
             in
               addAccum (parens ((fixity',fixity), whole), fixity', accum)
             end
      end (* GEN END FUN BRANCH *)

    | (* GEN BEGIN FUN BRANCH *) fmtLevel (G, d, Ctxt (fixity', accum, l),
                (OpArgs (fixity as (FX.Postfix _), fmts, S), s)) =
      let
          (* GEN BEGIN TAG OUTSIDE LET *) val accMore = eqFix (fixity', fixity) (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val pfx = if accMore andalso elide(l) then []
                    else if accMore andalso addots(l) then [F.Break, ldots]
                         else fmts (* GEN END TAG OUTSIDE LET *)
      in
        if accMore
          then fmtExp (G, d, Ctxt (fixity, pfx @ accum, l+1), fst(S, s))
        else let
               (* GEN BEGIN TAG OUTSIDE LET *) val whole = fmtExp (G, d, Ctxt (fixity, pfx, 0), fst (S, s)) (* GEN END TAG OUTSIDE LET *)
             in
               addAccum (parens ((fixity', fixity), whole), fixity', accum)
             end
      end (* GEN END FUN BRANCH *)

  (* braces (G, d, ((D, V), s)) = oa
     convert declaration D[s] as a prefix pi-abstraction into operator/arguments
     form with prefix "{D}" and argument V at printing depth d in printing
     context G approximating G'.

     Invariants:
      G' |- D[s] decl
      G' |- V : L  [NOTE: s does not apply to V!]
  *)
  and braces (G, d, ((D,V), s)) =
         OpArgs(FX.Prefix(binderPrec),
                [sym "{" , fmtDec (G, d, (D,s)), sym "}", F.Break],
                IntSyn.App(V, IntSyn.Nil))

  (* brackets (G, d, ((D, U), s)) = oa
     convert declaration D[s] as a prefix lambda-abstraction into operator/arguments
     form with prefix "[D]" and argument U at printing depth d in printing
     context G approximating G'.

     Invariants:
      G' |- D[s] decl
      G' |- U : V  [NOTE: s does not apply to U!]
  *)
  and brackets (G, d, ((D,U), s)) =
         OpArgs(FX.Prefix(binderPrec),
                [sym "[" , fmtDec (G, d, (D,s)), sym "]", F.Break],
                IntSyn.App(U, IntSyn.Nil))

  (* fmtDec (G, d, (D, s)) = fmt
     format declaration D[s] at printing depth d in printing context G approximating G'.

     Invariants:
      G' |- D[s] decl
  *)
  and (* GEN BEGIN FUN FIRST *) fmtDec (G, d, (I.Dec (x, V), s)) =
      F.HVbox [Str0 (Symbol.bvar (nameOf (x))), sym ":", fmtExp (G, d+1, noCtxt, (V,s))] (* GEN END FUN FIRST *)
      (* alternative with more whitespace *)
      (* F.HVbox [Str0 (Symbol.bvar (nameOf (x))), F.Space, sym ":", F.Break,
                  fmtExp (G, d+1, noCtxt, (V,s))]
      *)
    | (* GEN BEGIN FUN BRANCH *) fmtDec (G, d, (I.BDec (x, (cid, t)), s)) =
      let
        (* GEN BEGIN TAG OUTSIDE LET *) val (Gsome, Gblock) = I.constBlock cid (* GEN END TAG OUTSIDE LET *)
      in
        F.HVbox ([Str0 (Symbol.const (nameOf (x))), sym ":"]
                 @ fmtDecList' (G, (Gblock, I.comp (t, s))))
      end (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) fmtDec (G, d, (I.ADec (x, _), s)) =
      F.HVbox [Str0 (Symbol.bvar (nameOf (x))), sym ":_"] (* GEN END FUN BRANCH *)
     | (* GEN BEGIN FUN BRANCH *) fmtDec (G, d, (I.NDec (SOME name), s)) =
      F.HVbox [ sym name] (* GEN END FUN BRANCH *)
     (* alternative with more whitespace *)
      (* F.HVbox [Str0 (Symbol.bvar (nameOf (x))), F.Space, sym ":", F.Break,
                  fmtExp (G, d+1, noCtxt, (V,s))]
      *)
  and (* GEN BEGIN FUN FIRST *) fmtDecList' (G0, (nil, s)) = nil (* GEN END FUN FIRST *)
    | (* GEN BEGIN FUN BRANCH *) fmtDecList' (G0, (D::nil, s)) =
        sym "{" :: fmtDec (G0, 0, (D, s)) :: sym "}" :: nil (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) fmtDecList' (G0, (D::L, s)) =
        sym "{" :: fmtDec (G0, 0, (D, s)) :: sym "}" :: F.Break
        :: fmtDecList' (I.Decl (G0, D), (L, I.dot1 s)) (* GEN END FUN BRANCH *)

  fun (* GEN BEGIN FUN FIRST *) skipI (0, G, V) = (G, V) (* GEN END FUN FIRST *)
    | (* GEN BEGIN FUN BRANCH *) skipI (i, G, I.Pi ((D, _), V)) = skipI (i-1, I.Decl (G, Names.decEName (G, D)), V) (* GEN END FUN BRANCH *)

  fun (* GEN BEGIN FUN FIRST *) skipI2 (0, G, V, U) = (G, V, U) (* GEN END FUN FIRST *)
    | (* GEN BEGIN FUN BRANCH *) skipI2 (i, G, I.Pi ((D, _), V), I.Lam (D', U)) =
        skipI2 (i-1, I.Decl (G, Names.decEName (G, D')), V, U) (* GEN END FUN BRANCH *)

  fun (* GEN BEGIN FUN FIRST *) ctxToDecList (I.Null, L) = L (* GEN END FUN FIRST *)
    | (* GEN BEGIN FUN BRANCH *) ctxToDecList (I.Decl (G, D), L) = ctxToDecList (G, D::L) (* GEN END FUN BRANCH *)

  fun (* GEN BEGIN FUN FIRST *) fmtDecList (G0, nil) = nil (* GEN END FUN FIRST *)
    | (* GEN BEGIN FUN BRANCH *) fmtDecList (G0, D::nil) =
        sym"{"::fmtDec (G0, 0, (D, I.id))::sym"}"::nil (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) fmtDecList (G0, D::L) =
        sym"{"::fmtDec (G0, 0, (D, I.id))::sym"}"::F.Break
        ::fmtDecList (I.Decl (G0, D), L) (* GEN END FUN BRANCH *)

  (* Assume unique names are already assigned in G0 and G! *)
  fun fmtCtx (G0, G) = fmtDecList (G0, ctxToDecList (G, nil))


  fun (* GEN BEGIN FUN FIRST *) fmtBlock (I.Null, Lblock)=
        [sym "block", F.Break] @ (fmtDecList (I.Null, Lblock)) (* GEN END FUN FIRST *)
    | (* GEN BEGIN FUN BRANCH *) fmtBlock (Gsome, Lblock) =
        [F.HVbox ([sym "some", F.Space] @ (fmtCtx (I.Null, Gsome))),
         F.Break,
         F.HVbox ([sym "block", F.Space] @ (fmtDecList (Gsome, Lblock)))] (* GEN END FUN BRANCH *)

  (* fmtConDec (hide, condec) = fmt
     formats a constant declaration (which must be closed and in normal form)

     This function prints the quantifiers and abstractions only if hide = false.
  *)
  fun (* GEN BEGIN FUN FIRST *) fmtConDec (hide, condec as I.ConDec (_, _, imp, _, V, L)) =
      let
        (* GEN BEGIN TAG OUTSIDE LET *) val qid = Names.conDecQid condec (* GEN END TAG OUTSIDE LET *)
        (* GEN BEGIN TAG OUTSIDE LET *) val _ = Names.varReset IntSyn.Null (* GEN END TAG OUTSIDE LET *)
        (* GEN BEGIN TAG OUTSIDE LET *) val (G, V) = if hide then skipI (imp, I.Null, V) else (I.Null, V) (* GEN END TAG OUTSIDE LET *)
        (* GEN BEGIN TAG OUTSIDE LET *) val Vfmt = fmtExp (G, 0, noCtxt, (V, I.id)) (* GEN END TAG OUTSIDE LET *)
      in
        F.HVbox [fmtConstPath (Symbol.const, qid), F.Space, sym ":", F.Break, Vfmt, sym "."]
      end (* GEN END FUN FIRST *)
    | (* GEN BEGIN FUN BRANCH *) fmtConDec (hide, condec as I.SkoDec (_, _, imp, V, L)) =
      let
        (* GEN BEGIN TAG OUTSIDE LET *) val qid = Names.conDecQid condec (* GEN END TAG OUTSIDE LET *)
        (* GEN BEGIN TAG OUTSIDE LET *) val _ = Names.varReset IntSyn.Null (* GEN END TAG OUTSIDE LET *)
        (* GEN BEGIN TAG OUTSIDE LET *) val (G, V) = if hide then skipI (imp, I.Null, V) else (I.Null, V) (* GEN END TAG OUTSIDE LET *)
        (* GEN BEGIN TAG OUTSIDE LET *) val Vfmt = fmtExp (G, 0, noCtxt, (V, I.id)) (* GEN END TAG OUTSIDE LET *)
      in
        F.HVbox [sym "%skolem", F.Break, fmtConstPath (Symbol.skonst, qid), F.Space,
                 sym ":", F.Break, Vfmt, sym "."]
      end (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) fmtConDec (hide, condec as I.BlockDec (_, _, Gsome, Lblock)) =
      let
        (* GEN BEGIN TAG OUTSIDE LET *) val qid = Names.conDecQid condec (* GEN END TAG OUTSIDE LET *)
        (* GEN BEGIN TAG OUTSIDE LET *) val _ = Names.varReset IntSyn.Null (* GEN END TAG OUTSIDE LET *)
      in
        F.HVbox ([sym "%block", F.Break, fmtConstPath (Symbol.label, qid), F.Space,
                 sym ":", F.Break] @ (fmtBlock (Gsome, Lblock))  @ [sym "."])
      end (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) fmtConDec (hide, condec as I.BlockDef (_, _, W)) =
      let
        (* GEN BEGIN TAG OUTSIDE LET *) val qid = Names.conDecQid condec (* GEN END TAG OUTSIDE LET *)
        (* GEN BEGIN TAG OUTSIDE LET *) val _ = Names.varReset IntSyn.Null (* GEN END TAG OUTSIDE LET *)
      in
        F.HVbox ([sym "%block", F.Break, fmtConstPath (Symbol.label, qid), F.Space,
                 sym "=", F.Break] @ ( formatWorlds (T.Worlds W) :: [sym "."]))
      end (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) fmtConDec (hide, condec as I.ConDef (_, _, imp, U, V, L, _)) =
      (* reset variable names in between to align names of type V and definition U *)
      let
        (* GEN BEGIN TAG OUTSIDE LET *) val qid = Names.conDecQid condec (* GEN END TAG OUTSIDE LET *)
        (* GEN BEGIN TAG OUTSIDE LET *) val _ = Names.varReset IntSyn.Null (* GEN END TAG OUTSIDE LET *)
        (* GEN BEGIN TAG OUTSIDE LET *) val (G, V, U) = if hide then skipI2 (imp, I.Null, V, U) else (I.Null, V, U) (* GEN END TAG OUTSIDE LET *)
        (* GEN BEGIN TAG OUTSIDE LET *) val Vfmt = fmtExp (G, 0, noCtxt, (V, I.id)) (* GEN END TAG OUTSIDE LET *)
        (* val _ = Names.varReset () *)
        (* GEN BEGIN TAG OUTSIDE LET *) val Ufmt = fmtExp (G, 0, noCtxt, (U, I.id)) (* GEN END TAG OUTSIDE LET *)
      in
        F.HVbox [fmtConstPath (Symbol.def, qid), F.Space, sym ":", F.Break,
                         Vfmt, F.Break,
                         sym "=", F.Space,
                         Ufmt, sym "."]
    (* removed, when abbreviations where introduced. -- cs Mon Jun  7 16:03:30 EDT 1999
        F.Vbox0 0 1 [F.HVbox [Str0 (Symbol.def (name)), F.Space, sym ":", F.Break,
                         Vfmt, F.Break,
                         sym "=", F.Space,
                         Ufmt, sym "."],
                F.Break,
                F.HVbox [sym "%strict ", Str0 (Symbol.def (name)), sym "."]]
    *)      end (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) fmtConDec (hide, condec as I.AbbrevDef (_, _, imp, U, V, L)) =
      (* reset variable names in between to align names of type V and definition U *)
      let
        (* GEN BEGIN TAG OUTSIDE LET *) val qid = Names.conDecQid condec (* GEN END TAG OUTSIDE LET *)
        (* GEN BEGIN TAG OUTSIDE LET *) val _ = Names.varReset IntSyn.Null (* GEN END TAG OUTSIDE LET *)
        (* GEN BEGIN TAG OUTSIDE LET *) val (G, V, U) = if hide then skipI2 (imp, I.Null, V, U) else (I.Null, V, U) (* GEN END TAG OUTSIDE LET *)
        (* GEN BEGIN TAG OUTSIDE LET *) val Vfmt = fmtExp (G, 0, noCtxt, (V, I.id)) (* GEN END TAG OUTSIDE LET *)
        (* val _ = Names.varReset () *)
        (* GEN BEGIN TAG OUTSIDE LET *) val Ufmt = fmtExp (G, 0, noCtxt, (U, I.id)) (* GEN END TAG OUTSIDE LET *)
      in
        F.HVbox [fmtConstPath (Symbol.def, qid), F.Space, sym ":", F.Break,
                         Vfmt, F.Break,
                         sym "=", F.Space,
                         Ufmt, sym "."]
    (* removed, when abbreviations where introduced. -- cs Mon Jun  7 16:03:30 EDT 1999
        F.Vbox0 0 1 [F.HVbox [Str0 (Symbol.def (name)), F.Space, sym ":", F.Break,
                         Vfmt, F.Break,
                         sym "=", F.Space,
                         Ufmt, sym "."],
                F.Break,
                F.HVbox [sym "%nonstrict ", Str0 (Symbol.def (name)), sym "."]]
    *)      end (* GEN END FUN BRANCH *)

  fun (* GEN BEGIN FUN FIRST *) fmtCnstr (I.Solved) = [Str "Solved Constraint"] (* GEN END FUN FIRST *)
    | (* GEN BEGIN FUN BRANCH *) fmtCnstr (I.Eqn (G, U1, U2)) =
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val G' = Names.ctxLUName G (* GEN END TAG OUTSIDE LET *)
        in
          [F.HVbox [fmtExp (G', 0, noCtxt, (U1, I.id)),
                    F.Break, sym "=", F.Space,
                    fmtExp (G', 0, noCtxt, (U2, I.id))]]
        end (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) fmtCnstr (I.FgnCnstr (csfc as (cs, _))) =
        let
          fun (* GEN BEGIN FUN FIRST *) fmtExpL (nil) = [Str "Empty Constraint"] (* GEN END FUN FIRST *)
            | (* GEN BEGIN FUN BRANCH *) fmtExpL ((G, U) :: nil) =
                [fmtExp (Names.ctxLUName G, 0, noCtxt, (U, I.id))] (* GEN END FUN BRANCH *)
            | (* GEN BEGIN FUN BRANCH *) fmtExpL ((G,U) :: expL) =
                [fmtExp (Names.ctxLUName G, 0, noCtxt, (U, I.id)), Str ";", F.Break] @ fmtExpL expL (* GEN END FUN BRANCH *)
        in
          fmtExpL (I.FgnCnstrStd.ToInternal.apply csfc ())
        end (* GEN END FUN BRANCH *)

  fun (* GEN BEGIN FUN FIRST *) fmtCnstrL (nil) = [Str "Empty Constraint"] (* GEN END FUN FIRST *)
    | (* GEN BEGIN FUN BRANCH *) fmtCnstrL (ref Cnstr :: nil) = (fmtCnstr Cnstr) @ [Str "."] (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) fmtCnstrL (ref Cnstr :: cnstrL) =
        (fmtCnstr Cnstr) @ [Str ";", F.Break] @ (fmtCnstrL cnstrL) (* GEN END FUN BRANCH *)


  (* fmtNamedEVar, fmtEVarInst and evarInstToString are used to print
     instantiations of EVars occurring in queries.  To that end, a list of
     EVars paired with their is passed, thereby representing a substitution
     for logic variables.

     We always raise AVars to the empty context.
  *)
  fun (* GEN BEGIN FUN FIRST *) abstractLam (I.Null, U) = U (* GEN END FUN FIRST *)
    | (* GEN BEGIN FUN BRANCH *) abstractLam (I.Decl (G, D), U) = abstractLam (G, I.Lam (D, U)) (* GEN END FUN BRANCH *)

  fun (* GEN BEGIN FUN FIRST *) fmtNamedEVar (U as I.EVar(_,G,_,_), name) =
      let
        (* GEN BEGIN TAG OUTSIDE LET *) val U' = abstractLam (G, U) (* GEN END TAG OUTSIDE LET *)
      in
        F.HVbox [Str0 (Symbol.evar (name)), F.Space, sym "=", F.Break,
                 fmtExp (I.Null, 0, noCtxt, (U', I.id))]
      end (* GEN END FUN FIRST *)
    | (* GEN BEGIN FUN BRANCH *) fmtNamedEVar (U, name) = (* used for proof term variables in queries *)
      F.HVbox [Str0 (Symbol.evar (name)), F.Space, sym "=", F.Break,
               fmtExp (I.Null, 0, noCtxt, (U, I.id))] (* GEN END FUN BRANCH *)

  fun (* GEN BEGIN FUN FIRST *) fmtEVarInst (nil) = [Str "Empty Substitution"] (* GEN END FUN FIRST *)
    | (* GEN BEGIN FUN BRANCH *) fmtEVarInst ((U,name)::nil) = [fmtNamedEVar (U, name)] (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) fmtEVarInst ((U,name)::Xs) =
        fmtNamedEVar (U, name) :: Str ";" :: F.Break :: fmtEVarInst Xs (* GEN END FUN BRANCH *)

  (* collectEVars and collectConstraints are used to print constraints
     associated with EVars in a instantiation of variables occurring in queries.
  *)
  fun (* GEN BEGIN FUN FIRST *) collectEVars (nil, Xs) = Xs (* GEN END FUN FIRST *)
    | (* GEN BEGIN FUN BRANCH *) collectEVars ((U,_)::Xnames, Xs) =
        collectEVars (Xnames, Abstract.collectEVars (I.Null, (U, I.id), Xs)) (* GEN END FUN BRANCH *)

  fun eqCnstr r1 r2 = (r1 = r2)

  fun (* GEN BEGIN FUN FIRST *) mergeConstraints (nil, cnstrs2) = cnstrs2 (* GEN END FUN FIRST *)
    | (* GEN BEGIN FUN BRANCH *) mergeConstraints (cnstr::cnstrs1, cnstrs2) =
        if List.exists (eqCnstr cnstr) cnstrs2
          then mergeConstraints (cnstrs1, cnstrs2)
        else cnstr::(mergeConstraints (cnstrs1, cnstrs2)) (* GEN END FUN BRANCH *)

  fun (* GEN BEGIN FUN FIRST *) collectConstraints (nil) = nil (* GEN END FUN FIRST *)
    | (* GEN BEGIN FUN BRANCH *) collectConstraints (I.EVar(ref(NONE),_,_,cnstrs) :: Xs) =
        mergeConstraints (Constraints.simplify (!cnstrs),
                          collectConstraints Xs) (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) collectConstraints (_ :: Xs) = collectConstraints (Xs) (* GEN END FUN BRANCH *)

in

  (* In the functions below, G must be a "printing context", that is,
     (a) unique names must be assigned to each declaration which may
         actually applied in the scope (typically, using Names.decName)
     (b) types need not be well-formed, since they are not used
  *)
  fun formatDec (G, D) = fmtDec (G, 0, (D, I.id))
  fun formatDecList (G, D) = F.HVbox (fmtDecList (G, D))
  fun formatDecList' (G, (D,s)) = F.HVbox (fmtDecList' (G, (D, s)))
  fun formatExp (G, U) = fmtExp (G, 0, noCtxt, (U, I.id))
  fun formatSpine (G, S) = fmtSpine (G, 0, 0, (S, I.id))
  fun formatConDec (condec) = fmtConDec (false, condec)
  fun formatConDecI (condec) = fmtConDec (true, condec)
  fun formatCnstr (Cnstr) = F.Vbox0 0 1 (fmtCnstr Cnstr)
  fun formatCnstrs (cnstrL) = F.Vbox0 0 1 (fmtCnstrL cnstrL)
  fun formatCtx (G0, G) = F.HVbox (fmtCtx (G0, G))      (* assumes G0 and G are named *)

  fun decToString (G, D) = F.makestring_fmt (formatDec (G, D))
  fun expToString (G, U) = F.makestring_fmt (formatExp (G, U))
  fun conDecToString (condec) = F.makestring_fmt (formatConDec (condec))
  fun cnstrToString (Cnstr) = F.makestring_fmt (formatCnstr Cnstr)
  fun cnstrsToString (cnstrL) = F.makestring_fmt (formatCnstrs cnstrL)
  fun ctxToString (G0, G) = F.makestring_fmt (formatCtx (G0, G))

  fun evarInstToString Xnames =
        F.makestring_fmt (F.Hbox [F.Vbox0 0 1 (fmtEVarInst Xnames), Str "."])


  fun evarCnstrsToStringOpt Xnames =
      let
        (* GEN BEGIN TAG OUTSIDE LET *) val Ys = collectEVars (Xnames, nil) (* GEN END TAG OUTSIDE LET *)     (* collect EVars in instantiations *)
        (* GEN BEGIN TAG OUTSIDE LET *) val cnstrL = collectConstraints Ys (* GEN END TAG OUTSIDE LET *)
      in
        case cnstrL
          of nil => NONE
           | _ => SOME (cnstrsToString (cnstrL))
      end

  fun printSgn () =
      IntSyn.sgnApp ((* GEN BEGIN FUNCTION EXPRESSION *) fn (cid) => (print (F.makestring_fmt (formatConDecI (IntSyn.sgnLookup cid)));
                                  print "\n") (* GEN END FUNCTION EXPRESSION *))

    (* GEN BEGIN TAG OUTSIDE LET *) val formatWorlds = formatWorlds (* GEN END TAG OUTSIDE LET *)
    (* GEN BEGIN TAG OUTSIDE LET *) val worldsToString = worldsToString (* GEN END TAG OUTSIDE LET *)


end  (* local ... *)

end (* GEN END FUNCTOR DECL *)  (* functor Print *)
