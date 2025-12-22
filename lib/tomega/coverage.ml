(* Coverage checker for_sml programs *)

(* Author: Carsten Schuermann *)

module TomegaCoverage
    (TomegaPrint : TOMEGAPRINT)
    (TomegaTypeCheck : TOMEGATYPECHECK)
    (Cover : COVER) : TOMEGACOVERAGE = struct
  (*! structure IntSyn = IntSyn' !*)

  (*! structure Tomega = Tomega' !*)

  exception Error of string

  module I = IntSyn
  module T = Tomega
  (* chatter chlev f = ()

       Invariant:
       f () returns the string to be printed
         if current chatter level exceeds chlev
    *)

  let rec chatter chlev f =
    if !Global.chatter >= chlev then print ("[coverage] " ^ f ()) else ()
  (* purifyFor ((P, t), (Psi, F), s) = (t', Psi', s')

       Invariant:
       If    Psi0 |- t : Psi
       and   Psi0 |- P in F[t]
       and   Psi |- s : Psi1
       and   P == <M1, <M2, ... Mn, <>>>>
       and   F[t] = Ex x1:A1 ... Ex xn:An.true
       then  Psi' = Psi, x::A1, .... An
       and   t' = Mn...M1.t
       then  Psi0 |- t' : Psi'
       and   Psi' |- s' : Psi1
    *)

  let rec purifyFor = function
    | (T.Unit, t), (Psi, T.True), s -> (t, Psi, s)
    | (T.PairExp (U, P), t), (Psi, T.Ex ((D, _), F)), s ->
        purifyFor
          ( (P, T.Dot (T.Exp U, t)),
            (I.Decl (Psi, T.UDec D), F),
            T.comp (s, T.shift) )
  (*      | purifyFor ((T.Lam _, _), (_, _), _) = raise Domain
      | purifyFor ((T.New _, _), (_,  _), _) = raise Domain
      | purifyFor ((T.PairBlock _, _), (_,  _), _) = raise Domain
      | purifyFor ((T.PairPrg _, _), (_,  _), _) = raise Domain
      | purifyFor ((T.Unit, _), (_,  _), _) = raise Domain
      | purifyFor ((T.Root (T.Var k, _), _), (_,  _), _) = raise Domain
      | purifyFor ((T.Redex _, _), (_,  _), _) = raise Domain
      | purifyFor ((T.Rec _, _), (_,  _), _) = raise Domain
      | purifyFor ((T.Case _, _), (_,  _), _) = raise Domain
      | purifyFor ((T.PClo _, _), (_,  _), _) = raise Domain
      | purifyFor ((T.Let _, _), (_,  _), _) = raise Domain
      | purifyFor ((T.EVar _, _), (_,  _), _) = raise Domain
*)

  (*  | purifyFor (Psi, T.All (_, F), s) = (Psi, s)
        cannot occur by invariant Mon Dec  2 18:03:20 2002 -cs *)

  (* purifyCtx (t, Psi) = (t', Psi', s')
       If    Psi0 |- t : Psi
       then  Psi0 |- t' : Psi'
       and   Psi' |- s' : Psi
    *)

  let rec purifyCtx = function
    | t, Psi -> (t, Psi, T.id)
    | T.Dot (T.Prg P, t), I.Decl (Psi, T.PDec (_, T.All _, _, _)) ->
        let t', Psi', s' = purifyCtx (t, Psi) in
        (t', Psi', T.Dot (T.Undef, s'))
    | T.Dot (T.Prg (T.Var _), t), I.Decl (Psi, T.PDec (_, _, _, _)) ->
        let t', Psi', s' = purifyCtx (t, Psi) in
        (t', Psi', T.Dot (T.Undef, s'))
    | T.Dot (T.Prg (T.Const _), t), I.Decl (Psi, T.PDec (_, _, _, _)) ->
        let t', Psi', s' = purifyCtx (t, Psi) in
        (t', Psi', T.Dot (T.Undef, s'))
    | T.Dot (T.Prg (T.PairPrg (_, _)), t), I.Decl (Psi, T.PDec (_, _, _, _)) ->
        let t', Psi', s' = purifyCtx (t, Psi) in
        (t', Psi', T.Dot (T.Undef, s'))
    | T.Dot (T.Prg P, t), I.Decl (Psi, T.PDec (_, F, _, _)) ->
        let t', Psi', s' = purifyCtx (t, Psi) in
        let t'', Psi'', s'' =
          purifyFor ((P, t'), (Psi', T.forSub (F, s')), s')
        in
        (t'', Psi'', T.Dot (T.Undef, s''))
    | T.Dot (F, t), I.Decl (Psi, T.UDec D) ->
        let t', Psi', s' = purifyCtx (t, Psi) in
        ( T.Dot (F, t'),
          I.Decl (Psi', T.UDec (I.decSub (D, T.coerceSub s'))),
          T.dot1 s' )

  let rec purify (Psi0, t, Psi) =
    let t', Psi', s' = purifyCtx (t, Psi) in
    let _ = TomegaTypeCheck.checkSub (Psi0, t', Psi') in
    (Psi0, t', Psi')
  (* subToSpine (Psi', t, Psi) *)

  let rec coverageCheckPrg = function
    | W, Psi, T.Lam (D, P) -> coverageCheckPrg (W, I.Decl (Psi, D), P)
    | W, Psi, T.New P -> coverageCheckPrg (W, Psi, P)
    | W, Psi, T.PairExp (U, P) -> coverageCheckPrg (W, Psi, P)
    | W, Psi, T.PairBlock (B, P) -> coverageCheckPrg (W, Psi, P)
    | W, Psi, T.PairPrg (P1, P2) ->
        coverageCheckPrg (W, Psi, P1);
        coverageCheckPrg (W, Psi, P2)
    | W, Psi, T.Unit -> ()
    | W, Psi, T.Var _ -> ()
    | W, Psi, T.Const _ -> ()
    | W, Psi, T.Rec (D, P) -> coverageCheckPrg (W, I.Decl (Psi, D), P)
    | W, Psi, T.Case (T.Cases Omega) -> coverageCheckCases (W, Psi, Omega, [])
    | W, Psi, P ->
        coverageCheckPrg (W, Psi, P1);
        coverageCheckPrg (W, I.Decl (Psi, D), P2)
    | W, Psi, T.Redex (P, S) -> coverageCheckSpine (W, Psi, S)

  and coverageCheckSpine = function
    | W, Psi, T.Nil -> ()
    | W, Psi, T.AppExp (U, S) -> coverageCheckSpine (W, Psi, S)
    | W, Psi, T.AppBlock (B, S) -> coverageCheckSpine (W, Psi, S)
    | W, Psi, T.AppPrg (P, S) ->
        coverageCheckPrg (W, Psi, P);
        coverageCheckSpine (W, Psi, S)

  and coverageCheckCases = function
    | W, Psi, [], [] -> ()
    | W, Psi, [], Cs ->
        let _ =
          chatter 5 (fun () ->
              Int.toString (List.length Cs) ^ " cases to be checked\n")
        in
        let Cs' = map purify Cs in
        let Cs'' =
          map (fun (Psi0, t, _) -> (T.coerceCtx Psi0, T.coerceSub t)) Cs'
        in
        Cover.coverageCheckCases (W, Cs'', T.coerceCtx Psi')
    | W, Psi, (Psi', t, P) :: Omega, Cs ->
        coverageCheckPrg (W, Psi', P);
        coverageCheckCases (W, Psi, Omega, (Psi', t, Psi) :: Cs)

  let coverageCheckPrg = coverageCheckPrg
end
(* Unification on Formulas *)

(* Author: Carsten Schuermann *)

module type TOMEGACOVERAGE = sig
  (*! structure IntSyn : INTSYN !*)
  (*! structure Tomega : TOMEGA !*)
  exception Error of string

  val coverageCheckPrg :
    Tomega.worlds * Tomega.dec IntSyn.ctx * Tomega.prg -> unit
end

(* Signature TOMEGACOVERAGE *)
