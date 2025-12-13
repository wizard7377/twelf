(* Filling *)
(* Author: Carsten Schuermann *)
(* Date: Thu Mar 16 13:08:33 2006 *)

functor (* GEN BEGIN FUNCTOR DECL *) Fill
  (structure Data : DATA
   (*! structure IntSyn' : INTSYN !*)
   (*! structure Tomega' : TOMEGA !*)
   (*! sharing Tomega'.IntSyn = IntSyn' !*)
   structure State' : STATE
   (*! sharing State'.IntSyn = IntSyn' !*)
   (*! sharing State'.Tomega = Tomega' !*)
   structure Abstract : ABSTRACT
   (*! sharing Abstract.IntSyn = IntSyn' !*)
   (*! sharing Abstract.Tomega = Tomega' !*)
   structure TypeCheck : TYPECHECK
   (*! sharing TypeCheck.IntSyn = IntSyn' !*)
   structure Search  : SEARCH
   (*! sharing Search.IntSyn = IntSyn' !*)
   (*! sharing Search.Tomega = Tomega' !*)
     sharing Search.State = State'
   structure Whnf : WHNF
   (*! sharing Whnf.IntSyn = IntSyn' !*)
   structure Unify : UNIFY
   (*! sharing Unify.IntSyn = IntSyn' !*)

       )
     : FILL =
struct
  (*! structure IntSyn = IntSyn' !*)
  (*! structure Tomega = Tomega' !*)
  structure State = State'

  exception Error of string

  datatype operator =
    FillWithConst of IntSyn.exp * IntSyn.cid
       (* Representation Invariant:  FillWithConst (X, c) :
           X is an evar GX |- X : VX
           Sigma |- c : W
           and VX and W are unifiable
       *)
    | FillWithBVar of IntSyn.exp * int
       (* Representation Invariant:  FillWithBVar (X, n) :
           X is an evar GX |- X : VX
           GX |- n : W
           and VX and W are unifiable
       *)

  type operator = operator

  local
    structure S = State
    structure T = Tomega
    structure I = IntSyn

    exception Success of int


    (* expand' S = op'

       Invariant:
       If   |- S state
       then op' satifies representation invariant.
    *)
    fun expand (S.FocusLF (Y as I.EVar (r, G, V, _))) =   (* Y is lowered *)
      let
        fun (* GEN BEGIN FUN FIRST *) try (Vs as (I.Root _, _), Fs, O) =
          (CSManager.trail ((* GEN BEGIN FUNCTION EXPRESSION *) fn () => (Unify.unify (G, Vs, (V, I.id)); O :: Fs) (* GEN END FUNCTION EXPRESSION *))
           handle Unify.Unify _ => Fs) (* GEN END FUN FIRST *)
          | (* GEN BEGIN FUN BRANCH *) try ((I.Pi ((I.Dec (_, V1), _), V2), s), Fs, O) =
          let
            (* GEN BEGIN TAG OUTSIDE LET *) val X = I.newEVar (G, I.EClo (V1, s)) (* GEN END TAG OUTSIDE LET *)
          in
            try ((V2, I.Dot (I.Exp X, s)), Fs, O)
          end (* GEN END FUN BRANCH *)
          | (* GEN BEGIN FUN BRANCH *) try ((I.EClo (V, s'), s), Fs, O) = try ((V, I.comp (s', s)), Fs, O) (* GEN END FUN BRANCH *)
    
        (* matchCtx (G, n, Fs) = Fs'
    
           Invariant:
           If G0 = G, G' and |G'| = n and Fs a list of filling operators that
           satisfy the representation invariant, then Fs' is a list of filling operators
           that satisfy the representation invariant.
        *)
        fun (* GEN BEGIN FUN FIRST *) matchCtx (I.Null, _, Fs) = Fs (* GEN END FUN FIRST *)
          | (* GEN BEGIN FUN BRANCH *) matchCtx (I.Decl (G, I.Dec (x, V)), n, Fs) =
          matchCtx (G, n+1, try ((V, I.Shift (n+1)), Fs, FillWithBVar (Y, n+1))) (* GEN END FUN BRANCH *)
          | (* GEN BEGIN FUN BRANCH *) matchCtx (I.Decl (G, I.NDec _), n, Fs) =
          matchCtx (G, n+1, Fs) (* GEN END FUN BRANCH *)
    
        fun (* GEN BEGIN FUN FIRST *) matchSig (nil, Fs) = Fs (* GEN END FUN FIRST *)
          | (* GEN BEGIN FUN BRANCH *) matchSig (I.Const (c)::L, Fs) =
          matchSig (L, try ((I.constType (c), I.id), Fs, FillWithConst (Y, c))) (* GEN END FUN BRANCH *)
      in
        matchCtx (G, 0, matchSig (Index.lookup (I.targetFam V), nil))
      end

    (* apply op = ()

       Invariant:
       If op is a filling operator that satisfies the representation invariant.
       The apply operation is guaranteed to always succeed.
    *)
    fun (* GEN BEGIN FUN FIRST *) apply (FillWithBVar(Y as I.EVar (r, G, V, _), n)) = (* Y is lowered *)
      let
        (* Invariant : G |- s : G'   G' |- V : type *)
        fun (* GEN BEGIN FUN FIRST *) doit (Vs as (I.Root _, _),  k) =
            (Unify.unify (G, Vs, (V, I.id)); (k I.Nil)) (* GEN END FUN FIRST *)  (* Unify must succeed *)
          | (* GEN BEGIN FUN BRANCH *) doit ((I.Pi ((I.Dec (_, V1), _), V2), s), k) =
            let
              (* GEN BEGIN TAG OUTSIDE LET *) val X = I.newEVar (G, I.EClo (V1, s)) (* GEN END TAG OUTSIDE LET *)
            in
              doit ((V2, I.Dot (I.Exp X, s)),  ((* GEN BEGIN FUNCTION EXPRESSION *) fn S => k (I.App (X, S)) (* GEN END FUNCTION EXPRESSION *)))
            end (* GEN END FUN BRANCH *)
          | (* GEN BEGIN FUN BRANCH *) doit ((I.EClo (V, t), s), k) = doit ((V, I.comp (t, s)), k) (* GEN END FUN BRANCH *)
    
        (* GEN BEGIN TAG OUTSIDE LET *) val I.Dec (_, W) = I.ctxDec (G, n) (* GEN END TAG OUTSIDE LET *)
      in
        doit ((W, I.id),  (* GEN BEGIN FUNCTION EXPRESSION *) fn S => Unify.unify (G, (Y, I.id), (I.Root (I.BVar n, S), I.id)) (* GEN END FUNCTION EXPRESSION *))
      end (* GEN END FUN FIRST *)
    | (* GEN BEGIN FUN BRANCH *) apply (FillWithConst(Y as I.EVar (r, G0, V, _), c)) =
      let
        fun (* GEN BEGIN FUN FIRST *) doit (Vs as (I.Root _, _),  k) =
            (Unify.unify (G0, Vs, (V, I.id)); (k I.Nil)) (* GEN END FUN FIRST *)  (* Unify must succeed *)
          | (* GEN BEGIN FUN BRANCH *) doit ((I.Pi ((I.Dec (_, V1), _), V2), s), k) =
            let
              (* GEN BEGIN TAG OUTSIDE LET *) val X = I.newEVar (G0, I.EClo (V1, s)) (* GEN END TAG OUTSIDE LET *)
            in
              doit ((V2, I.Dot (I.Exp X, s)),  ((* GEN BEGIN FUNCTION EXPRESSION *) fn S => k (I.App (X, S)) (* GEN END FUNCTION EXPRESSION *)))
            end (* GEN END FUN BRANCH *)
        (* GEN BEGIN TAG OUTSIDE LET *) val W = I.constType c (* GEN END TAG OUTSIDE LET *)
      in
        doit ((W, I.id),  (* GEN BEGIN FUNCTION EXPRESSION *) fn S => Unify.unify (G0, (Y, I.id), (I.Root (I.Const c, S), I.id)) (* GEN END FUNCTION EXPRESSION *))
      end (* GEN END FUN BRANCH *)

    (* menu op = s'

       Invariant:
       If op is a filling operator
       then s' is a string describing the operation in plain text
    *)
    fun (* GEN BEGIN FUN FIRST *) menu (FillWithBVar (X as I.EVar (_, G, _, _), n)) =
        (case (I.ctxLookup (Names.ctxName G, n))
          of I.Dec (SOME x, _) =>
            ("Fill " ^ Names.evarName (G, X) ^ " with variable " ^ x)) (* GEN END FUN FIRST *)
           (* Invariant: Context is named  --cs Fri Mar  3 14:31:08 2006 *)
      | (* GEN BEGIN FUN BRANCH *) menu (FillWithConst (X as I.EVar (_, G, _, _), c)) =
           ("Fill " ^ Names.evarName (G, X) ^ " with constant " ^ IntSyn.conDecName (IntSyn.sgnLookup c)) (* GEN END FUN BRANCH *)

  in
    (* GEN BEGIN TAG OUTSIDE LET *) val expand = expand (* GEN END TAG OUTSIDE LET *)
    (* GEN BEGIN TAG OUTSIDE LET *) val apply = apply (* GEN END TAG OUTSIDE LET *)
    (* GEN BEGIN TAG OUTSIDE LET *) val menu = menu (* GEN END TAG OUTSIDE LET *)
  end (* local *)
end (* GEN END FUNCTOR DECL *); (* functor Filling *)
