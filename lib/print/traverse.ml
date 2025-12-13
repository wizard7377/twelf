functor (* GEN BEGIN FUNCTOR DECL *) Traverse
  ((*! structure IntSyn' : INTSYN !*)
   structure Whnf : WHNF
   (*! sharing Whnf.IntSyn = IntSyn' !*)
   structure Names : NAMES
   (*! sharing Names.IntSyn = IntSyn' !*)
   structure Traverser' : TRAVERSER)
  : TRAVERSE
  (* shares types from Traverser' *)
=
struct

  (*! structure IntSyn = IntSyn' !*)
  structure Traverser = Traverser'

  exception Error of string

local

  structure I = IntSyn
  structure T = Traverser

  (* from typecheck.fun *)

  (* inferCon (G, C) = V'

     Invariant:
     If    G |- C : V
     and  (C  doesn't contain FVars)
     then  G' |- V' : L      (for some level L)
     and   G |- V = V' : L
     else exception Error is raised.
  *)
  fun (* GEN BEGIN FUN FIRST *) inferConW (G, I.BVar (k')) =
      let
        (* GEN BEGIN TAG OUTSIDE LET *) val I.Dec (_,V) = I.ctxDec (G, k') (* GEN END TAG OUTSIDE LET *)
      in
        Whnf.whnf (V, I.id)
      end (* GEN END FUN FIRST *)
    | (* GEN BEGIN FUN BRANCH *) inferConW (G, I.Const(c)) = (I.constType (c), I.id) (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) inferConW (G, I.Def(d))  = (I.constType (d), I.id) (* GEN END FUN BRANCH *)
    (* no case for FVar, Skonst *)

  fun (* GEN BEGIN FUN FIRST *) fromHead (G, I.BVar(n)) = T.bvar (Names.bvarName (G, n)) (* GEN END FUN FIRST *)
    | (* GEN BEGIN FUN BRANCH *) fromHead (G, I.Const(cid)) =
      let
        (* GEN BEGIN TAG OUTSIDE LET *) val Names.Qid (ids, id) = Names.constQid (cid) (* GEN END TAG OUTSIDE LET *)
      in
        T.const (ids, id)
      end (* GEN END FUN BRANCH *)
    (* | fromHead (G, I.Skonst (cid)) = T.skonst (Names.constName (cid)) *)
    | (* GEN BEGIN FUN BRANCH *) fromHead (G, I.Def (cid)) =
      let
        (* GEN BEGIN TAG OUTSIDE LET *) val Names.Qid (ids, id) = Names.constQid (cid) (* GEN END TAG OUTSIDE LET *)
      in
        T.def (ids, id)
      end (* GEN END FUN BRANCH *)
    (* | fromHead (G, FVar (name, _, _)) = T.fvar (name) *)
    | (* GEN BEGIN FUN BRANCH *) fromHead _ = raise Error ("Head not recognized") (* GEN END FUN BRANCH *)

  (* see also: print.fun *)
  fun (* GEN BEGIN FUN FIRST *) impCon (I.Const (cid)) = I.constImp (cid) (* GEN END FUN FIRST *)
    (*| imps (I.Skonst (cid)) = I.constImp (cid) *)
    | (* GEN BEGIN FUN BRANCH *) impCon (I.Def (cid)) = I.constImp (cid) (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) impCon _ = 0 (* GEN END FUN BRANCH *)

  (* see also: print.fun *)
  (*
  fun dropImp (0, S) = S
    | dropImp (i, I.App (U, S)) = dropImp (i-1, S)
    | dropImp (i, I.SClo (S, s)) = I.SClo (dropImp (i, S), s)
    | dropImp _ = raise Error ("Missing implicit arguments")
  *)

  fun (* GEN BEGIN FUN FIRST *) fromTpW (G, (I.Root (C, S), s)) =
        T.atom (fromHead (G, C),
                fromSpine (impCon C, G, (S, s), inferConW (G, C))) (* GEN END FUN FIRST *)
    | (* GEN BEGIN FUN BRANCH *) fromTpW (G, (I.Pi ((D as I.Dec(_,V1), I.No), V2), s)) =
        T.arrow (fromTp (G, (V1, s)),
                 fromTp (I.Decl (G, I.decSub (D, s)), (V2, I.dot1 s))) (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) fromTpW (G, (I.Pi ((D, I.Maybe), V2), s)) =
      let
        (* GEN BEGIN TAG OUTSIDE LET *) val D' = Names.decUName (G, D) (* GEN END TAG OUTSIDE LET *)
      in
        T.pi (fromDec (G, (D', s)),
              fromTp (I.Decl (G, I.decSub (D', s)), (V2, I.dot1 s)))
      end (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) fromTpW _ = raise Error ("Type not recognized") (* GEN END FUN BRANCH *)

  and fromTp (G, Vs) = fromTpW (G, Whnf.whnf Vs)

  and (* GEN BEGIN FUN FIRST *) fromObjW (G, (I.Root (C, S), s), (V, t)) =
        T.root (fromHead (G, C),
                fromSpine (impCon C, G, (S, s), inferConW (G, C)),
                fromTp (G, (V, t))) (* GEN END FUN FIRST *)
    | (* GEN BEGIN FUN BRANCH *) fromObjW (G, (I.Lam (D, U), s), (I.Pi (_, V), t)) =
      let
        (* GEN BEGIN TAG OUTSIDE LET *) val D' = Names.decUName (G, D) (* GEN END TAG OUTSIDE LET *)
      in
        T.lam (fromDec (G, (D', s)),
               fromObj (I.Decl (G, I.decSub (D', s)),
                        (U, I.dot1 s),
                        (V, I.dot1 t)))
      end (* GEN END FUN BRANCH *)
    (* note: no case for EVars right now *)
    | (* GEN BEGIN FUN BRANCH *) fromObjW _ = raise Error ("Object not recognized") (* GEN END FUN BRANCH *)

  and fromObj (G, Us, Vt) = fromObjW (G, Whnf.whnf Us, Whnf.whnf Vt)

  and (* GEN BEGIN FUN FIRST *) fromSpine (i, G, (I.Nil, s), Vt) = T.nils (* GEN END FUN FIRST *)
    | (* GEN BEGIN FUN BRANCH *) fromSpine (i, G, (I.SClo (S, s'), s), Vt) =
        fromSpine (i, G, (S, I.comp (s', s)), Vt) (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) fromSpine (i, G, (I.App (U, S), s),
                 (I.Pi ((I.Dec (_, V1), _), V2), t)) =
      if i > 0                          (* drop implicit arg *)
        then fromSpine (i-1, G, (S, s),
                        Whnf.whnf (V2, I.Dot (I.Exp (I.EClo (U, s)), t)))
      else
        T.app (fromObj (G, (U, s), (V1, t)),
               fromSpine (i, G, (S, s),
                          Whnf.whnf (V2, I.Dot (I.Exp (I.EClo (U, s)), t)))) (* GEN END FUN BRANCH *)

  and fromDec (G, (I.Dec (SOME(x), V), s)) =
        T.dec (x, fromTp (G, (V, s)))
    (* NONE should not occur because of call to decName *)
    (*
    | fromDec (G, (I.Dec (NONE, V), s)) =
        T.dec ("_", fromTp (G, (V, s)))
    *)

  (* ignore a : K, d : A = M, b : K = A, and skolem constants *)
  fun (* GEN BEGIN FUN FIRST *) fromConDec (I.ConDec (c, parent, i, _, V, I.Type)) =
        SOME (T.objdec (c, fromTp (I.Null, (V, I.id)))) (* GEN END FUN FIRST *)
    | (* GEN BEGIN FUN BRANCH *) fromConDec _ = NONE (* GEN END FUN BRANCH *)

in

  (* GEN BEGIN TAG OUTSIDE LET *) val fromConDec = fromConDec (* GEN END TAG OUTSIDE LET *)

  fun const (name) =
      let (* GEN BEGIN TAG OUTSIDE LET *) val qid = case Names.stringToQid name
                      of NONE => raise Error ("Malformed qualified identifier " ^ name)
                       | SOME qid => qid (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val cidOpt = Names.constLookup qid (* GEN END TAG OUTSIDE LET *)
          fun (* GEN BEGIN FUN FIRST *) getConDec (NONE) = raise Error ("Undeclared identifier " ^ Names.qidToString qid) (* GEN END FUN FIRST *)
            | (* GEN BEGIN FUN BRANCH *) getConDec (SOME cid) = IntSyn.sgnLookup cid (* GEN END FUN BRANCH *)
          (* GEN BEGIN TAG OUTSIDE LET *) val conDec = getConDec cidOpt (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val _ = Names.varReset IntSyn.Null (* GEN END TAG OUTSIDE LET *)
          fun (* GEN BEGIN FUN FIRST *) result (NONE) = raise Error ("Wrong kind of declaration") (* GEN END FUN FIRST *)
            | (* GEN BEGIN FUN BRANCH *) result (SOME(r)) = r (* GEN END FUN BRANCH *)
      in
        result (fromConDec conDec)
      end

end  (* local ... *)

end (* GEN END FUNCTOR DECL *);  (* functor Traverse *)
