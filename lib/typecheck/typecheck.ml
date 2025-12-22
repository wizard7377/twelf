(* Type Checking *)

(* Author: Carsten Schuermann *)

module TypeCheck (Conv : CONV) (Whnf : WHNF) (Names : NAMES) (Print : PRINT) :
  TYPECHECK = struct
  (*! structure IntSyn = IntSyn' !*)

  exception Error of string

  module I = IntSyn
  (* for_sml debugging purposes *)

  let rec subToString = function
    | G, I.Dot (I.Idx n, s) -> Int.toString n ^ "." ^ subToString (G, s)
    | G, I.Dot (I.Exp U, s) ->
        "(" ^ Print.expToString (G, U) ^ ")." ^ subToString (G, s)
    | G, I.Dot (I.Block L, s) -> LVarToString (G, L) ^ "." ^ subToString (G, s)
    | G, I.Shift n -> "^" ^ Int.toString n

  and LVarToString = function
    | G, I.LVar ({ contents = Some B }, sk, (l, t)) ->
        LVarToString (G, I.blockSub (B, sk))
    | G, I.LVar ({ contents = None }, sk, (cid, t)) ->
        "#" ^ I.conDecName (I.sgnLookup cid) ^ "[" ^ subToString (G, t) ^ "]"
  (* some well-formedness conditions are assumed for_sml input expressions *)

  (* e.g. don't contain "Kind", Evar's are consistently instantiated, ... *)

  (* checkExp (G, (U, s1), (V2, s2)) = ()

       Invariant:
       If   G |- s1 : G1
       and  G |- s2 : G2    G2 |- V2 : L
       returns () if there is a V1 s.t.
            G1 |- U : V1
       and  G  |- V1 [s1] = V2 [s2] : L
       otherwise exception Error is raised
    *)

  let rec checkExp (G, Us, Vs) =
    let Us' = inferExp (G, Us) in
    if Conv.conv (Us', Vs) then () else raise (Error "Type mismatch")

  and inferUni I.Type = I.Kind

  and inferExpW = function
    | G, (I.Uni L, _) -> (I.Uni (inferUni L), I.id)
    | G, (I.Pi ((D, _), V), s) ->
        checkDec (G, (D, s));
        inferExp (I.Decl (G, I.decSub (D, s)), (V, I.dot1 s))
    | G, (I.Root (C, S), s) ->
        inferSpine (G, (S, s), Whnf.whnf (inferCon (G, C), I.id))
    | G, (I.Lam (D, U), s) ->
        checkDec (G, (D, s));
        ( I.Pi
            ( (I.decSub (D, s), I.Maybe),
              I.EClo (inferExp (I.Decl (G, I.decSub (D, s)), (U, I.dot1 s))) ),
          I.id )
    | G, (I.FgnExp csfe, s) ->
        inferExp (G, (I.FgnExpStd.ToInternal.apply csfe (), s))

  and inferExp (G, Us) = inferExpW (G, Whnf.whnf Us)

  and inferSpine = function
    | G, (I.Nil, _), Vs -> Vs
    | G, (I.SClo (S, s'), s), Vs -> inferSpine (G, (S, I.comp (s', s)), Vs)
    | G, (I.App (U, S), s1), (I.Pi ((I.Dec (_, V1), _), V2), s2) ->
        checkExp (G, (U, s1), (V1, s2));
        inferSpine
          (G, (S, s1), Whnf.whnf (V2, I.Dot (I.Exp (I.EClo (U, s1)), s2)))
    | G, Ss, Vs -> inferSpine (G, Ss, Whnf.expandDef Vs)
    | G, (I.App (U, S), _), (V, s) ->
        raise (Error "Expression is applied, but not a function")

  and inferCon = function
    | G, I.BVar k' ->
        let (I.Dec (_, V)) = I.ctxDec (G, k') in
        V
    | G, I.Proj (B, i) ->
        let (I.Dec (_, V)) = I.blockDec (G, B, i) in
        V
    | G, I.Const c -> I.constType c
    | G, I.Def d -> I.constType d
    | G, I.Skonst c -> I.constType c
    | G, I.FgnConst (cs, conDec) -> I.conDecType conDec

  and typeCheck (G, (U, V)) =
    checkCtx G;
    checkExp (G, (U, I.id), (V, I.id))

  and checkSub = function
    | I.Null, I.Shift 0, I.Null -> ()
    | I.Decl (G, D), I.Shift k, I.Null ->
        if k > 0 then checkSub (G, I.Shift (k - 1), I.Null)
        else raise (Error "Substitution not well-typed")
    | G', I.Shift k, G ->
        checkSub (G', I.Dot (I.Idx (k + 1), I.Shift (k + 1)), G)
    | G', I.Dot (I.Idx k, s'), I.Decl (G, I.Dec (_, V2)) ->
        let _ = checkSub (G', s', G) in
        let (I.Dec (_, V1)) = I.ctxDec (G', k) in
        if Conv.conv ((V1, I.id), (V2, s')) then ()
        else
          raise
            (Error
               ("Substitution not well-typed \n  found: "
               ^ Print.expToString (G', V1)
               ^ "\n  expected: "
               ^ Print.expToString (G', I.EClo (V2, s'))))
    | G', I.Dot (I.Exp U, s'), I.Decl (G, I.Dec (_, V2)) ->
        let _ = checkSub (G', s', G) in
        let _ = typeCheck (G', (U, I.EClo (V2, s'))) in
        ()
    | G', I.Dot (I.Idx w, t), I.Decl (G, I.BDec (_, (l, s))) ->
        (* G' |- s' : GSOME *)
        (* G  |- s  : GSOME *)
        (* G' |- t  : G       (verified below) *)
        let _ = checkSub (G', t, G) in
        let (I.BDec (_, (l', s'))) = I.ctxDec (G', w) in
        if l <> l' then raise (Error "Incompatible block labels found")
        else if Conv.convSub (I.comp (s, t), s') then ()
        else raise (Error "Substitution in block declaration not well-typed")
    | G', I.Dot (I.Block (I.Inst I), t), I.Decl (G, I.BDec (_, (l, s))) ->
        let _ = checkSub (G', t, G) in
        let G, L = I.constBlock l in
        let _ = checkBlock (G', I, (I.comp (s, t), L)) in
        ()
    | G', s, I.Null ->
        raise (Error ("Long substitution" ^ "\n" ^ subToString (G', s)))

  and checkBlock = function
    | G, [], (_, []) -> ()
    | G, U :: I, (t, I.Dec (_, V) :: L) ->
        checkExp (G, (U, I.id), (V, t));
        checkBlock (G, I, (I.Dot (I.Exp U, t), L))

  and checkDec = function
    | G, (I.Dec (_, V), s) -> checkExp (G, (V, s), (I.Uni I.Type, I.id))
    | G, (I.BDec (_, (c, t)), s) ->
        (* G1 |- t : GSOME *)
        (* G  |- s : G1 *)
        let Gsome, piDecs = I.constBlock c in
        checkSub (G, I.comp (t, s), Gsome)
    | G, (NDec, _) -> ()

  and checkCtx = function
    | I.Null -> ()
    | I.Decl (G, D) ->
        checkCtx G;
        checkDec (G, (D, I.id))

  let rec check (U, V) = checkExp (I.Null, (U, I.id), (V, I.id))
  let rec infer U = I.EClo (inferExp (I.Null, (U, I.id)))
  let rec infer' (G, U) = I.EClo (inferExp (G, (U, I.id)))

  let rec checkConv (U1, U2) =
    if Conv.conv ((U1, I.id), (U2, I.id)) then ()
    else
      raise
        (Error
           ("Terms not equal\n  left: "
           ^ Print.expToString (I.Null, U1)
           ^ "\n  right:"
           ^ Print.expToString (I.Null, U2)))

  let check = check
  let checkDec = checkDec
  let checkConv = checkConv
  let infer = infer
  let infer' = infer'
  let typeCheck = typeCheck
  let typeCheckCtx = checkCtx
  let typeCheckSub = checkSub
  (* local ... *)
end

(* functor TypeCheck *)
