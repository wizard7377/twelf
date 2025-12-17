TomegaCoverage  TomegaPrint TOMEGAPRINT    TomegaTypeCheck TOMEGATYPECHECK    Cover COVER     TOMEGACOVERAGE  struct (*! structure IntSyn = IntSyn' !*)
(*! structure Tomega = Tomega' !*)
exception module module (* chatter chlev f = ()

       Invariant:
       f () returns the string to be printed
         if current chatter level exceeds chlev
    *)
let rec chatterchlevf if ! chatter >= chlev then print ("[coverage] " ^ f ()) else ()(* purifyFor ((P, t), (Psi, F), s) = (t', Psi', s')

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
let rec purifyFor((unit,  , t),  , (psi,  , true),  , s) (t,  , psi,  , s) purifyFor((pairExp (u,  , p),  , t),  , (psi,  , ex ((d,  , _),  , f)),  , s) purifyFor ((p,  , dot (exp u,  , t)),  , (decl (psi,  , uDec d),  , f),  , comp (s,  , shift))(*      | purifyFor ((T.Lam _, _), (_, _), _) = raise Domain
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
let rec purifyCtx(t as shift k,  , psi) (t,  , psi,  , id) purifyCtx(dot (prg p,  , t),  , decl (psi,  , pDec (_,  , all _,  , _,  , _))) let let  in in (t',  , psi',  , dot (undef,  , s')) purifyCtx(dot (prg (var _),  , t),  , decl (psi,  , pDec (_,  , _,  , _,  , _))) let let  in in (t',  , psi',  , dot (undef,  , s')) purifyCtx(dot (prg (const _),  , t),  , decl (psi,  , pDec (_,  , _,  , _,  , _))) let let  in in (t',  , psi',  , dot (undef,  , s')) purifyCtx(dot (prg (pairPrg (_,  , _)),  , t),  , decl (psi,  , pDec (_,  , _,  , _,  , _))) let let  in in (t',  , psi',  , dot (undef,  , s')) purifyCtx(dot (prg p,  , t),  , decl (psi,  , pDec (_,  , f,  , _,  , _))) let let  inlet  in in (t'',  , psi'',  , dot (undef,  , s'')) purifyCtx(dot (f,  , t),  , decl (psi,  , uDec d)) let let  in in (dot (f,  , t'),  , decl (psi',  , uDec (decSub (d,  , coerceSub s'))),  , dot1 s')let rec purify(psi0,  , t,  , psi) let let  inlet  in in (psi0,  , t',  , psi')(* subToSpine (Psi', t, Psi) *)
let rec coverageCheckPrg(w,  , psi,  , lam (d,  , p)) coverageCheckPrg (w,  , decl (psi,  , d),  , p) coverageCheckPrg(w,  , psi,  , new p) coverageCheckPrg (w,  , psi,  , p) coverageCheckPrg(w,  , psi,  , pairExp (u,  , p)) coverageCheckPrg (w,  , psi,  , p) coverageCheckPrg(w,  , psi,  , pairBlock (b,  , p)) coverageCheckPrg (w,  , psi,  , p) coverageCheckPrg(w,  , psi,  , pairPrg (p1,  , p2)) (coverageCheckPrg (w,  , psi,  , p1); coverageCheckPrg (w,  , psi,  , p2)) coverageCheckPrg(w,  , psi,  , unit) () coverageCheckPrg(w,  , psi,  , var _) () coverageCheckPrg(w,  , psi,  , const _) () coverageCheckPrg(w,  , psi,  , rec (d,  , p)) coverageCheckPrg (w,  , decl (psi,  , d),  , p) coverageCheckPrg(w,  , psi,  , case (cases omega)) coverageCheckCases (w,  , psi,  , omega,  , nil) coverageCheckPrg(w,  , psi,  , p as let (d,  , p1,  , p2)) (coverageCheckPrg (w,  , psi,  , p1); (* chatter 5 ("fn () => TomegaPrint.prgToString (Psi, P)); *)
coverageCheckPrg (w,  , decl (psi,  , d),  , p2)) coverageCheckPrg(w,  , psi,  , redex (p,  , s)) coverageCheckSpine (w,  , psi,  , s)(*    | coverageCheckPrg (Psi, T.EVar) =
          should not occur by invariant  *)
 coverageCheckSpine(w,  , psi,  , nil) () coverageCheckSpine(w,  , psi,  , appExp (u,  , s)) coverageCheckSpine (w,  , psi,  , s) coverageCheckSpine(w,  , psi,  , appBlock (b,  , s)) coverageCheckSpine (w,  , psi,  , s) coverageCheckSpine(w,  , psi,  , appPrg (p,  , s)) (coverageCheckPrg (w,  , psi,  , p); coverageCheckSpine (w,  , psi,  , s))(*    | coverageCheckSpine (Psi, T.SClo _) =
          should not occur by invariant  *)
 coverageCheckCases(w,  , psi,  , nil,  , nil) () coverageCheckCases(w,  , psi,  , nil,  , cs) let let  inlet  inlet  in in coverageCheckCases (w,  , cs'',  , coerceCtx psi') coverageCheckCases(w,  , psi,  , (psi',  , t,  , p) :: omega,  , cs) (coverageCheckPrg (w,  , psi',  , p); coverageCheckCases (w,  , psi,  , omega,  , (psi',  , t,  , psi) :: cs))let  inend