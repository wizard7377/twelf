TomegaPrint  Formatter FORMATTER    Names NAMES    Print PRINT    Print Formatter  Formatter    TOMEGAPRINT  struct (*! structure IntSyn = IntSyn' !*)
(*! structure Tomega = Tomega' !*)
module exception (* is just here because we don't have a
     module yet for names. move later
     --cs Tue Apr 27 12:04:45 2004 *)
module module module module (* Invariant:

       The proof term must satisfy the following conditions:
       * proof term must have the structure
           Rec.     Lam ... Lam Case
                And Lam ... Lam Case
                ...
                And Lam ... Lam Case
         and the body of every case must be of the form
           (Let Decs in Case ...
           or
           Inx ... Inx Unit) *
         where Decs are always of the form
           New ... New App .. App Split .. Split Empty
     *)
let  inlet rec evarReset() (evarList := nil)let rec evarNamen let let rec evarName'nil raise (error "not found") evarName'((y as eVar (_,  , _,  , _,  , _,  , _,  , x as eVar (_,  , g,  , r,  , _))) :: l) if evarName (g,  , x) = n then y else evarName' l in evarName' (! evarList)let rec nameEVar(eVar (_,  , _,  , _,  , _,  , _,  , x as eVar (_,  , g,  , r,  , _))) evarName (g,  , x)(* formatCtxBlock (G, (G1, s1)) = (G', s', fmts')

       Invariant:
       If   |- G ctx
       and  G |- G1 ctx
       and  G2 |- s1 : G
       then G' = G2, G1 [s1]
       and  G' |- s' : G, G1
       and  fmts is a format list of G1[s1]
    *)
let rec formatCtxBlock(g,  , (null,  , s)) (g,  , s,  , nil) formatCtxBlock(g,  , (decl (null,  , d),  , s)) let let  inlet  in in (decl (g,  , d'),  , dot1 s,  , [fmt]) formatCtxBlock(g,  , (decl (g',  , d),  , s)) let let  inlet  inlet  in in (decl (g'',  , d''),  , dot1 s'',  , fmts @ [string ","; break; fmt])let rec constNamec conDecName (sgnLookup c)let rec formatWorldnil [] formatWorld[c] [string (constName c)] formatWorld(c :: cids) [string (constName c); string ","; break] @ formatWorld cids(* formatFor' (G, (F, s)) = fmts'

       Invariant:
       If   |- G ctx
       and  G |- s : Psi'
       and  Psi' |- F formula
       then fmts' is a list of formats for F
    *)
let rec formatFor'(psi,  , all ((d,  , explicit),  , f)) (match d with uDec d -> let let  inlet  in in [string "all {"; formatDec (g,  , d'); string "}"; break] @ formatFor' (decl (psi,  , uDec d'),  , f)) formatFor'(psi,  , all ((d,  , implicit),  , f)) (match d with uDec d -> let let  inlet  in in [string "all^ {"; formatDec (g,  , d'); string "}"; break] @ formatFor' (decl (psi,  , uDec d'),  , f)) formatFor'(psi,  , ex ((d,  , explicit),  , f)) let let  inlet  in in [string "exists {"; formatDec (g,  , d'); string "}"; break] @ formatFor' (decl (psi,  , uDec d'),  , f) formatFor'(psi,  , ex ((d,  , implicit),  , f)) let let  inlet  in in [string "exists^ {"; formatDec (g,  , d'); string "}"; break] @ formatFor' (decl (psi,  , uDec d'),  , f) formatFor'(psi,  , and (f1,  , f2)) [string "("; hVbox (formatFor' (psi,  , f1)); string ")"; break; string "/\\"; space; string "("; hVbox (formatFor' (psi,  , f2)); string ")"] formatFor'(psi,  , true) [string "true"] formatFor'(psi,  , world (worlds l,  , f)) [string "world ("; hVbox (formatWorld l); string ")"; break] @ formatFor' (psi,  , f)let rec formatFor(g,  , f) hVbox (formatFor' (g,  , forSub (f,  , id)))let rec forToString(psi,  , f) makestring_fmt (formatFor (psi,  , f))(* formatPrg (Psi, P) names = fmt'

       Invariant:
       If   |- Psi ctx
       and  Psi; . |- P = rec x. (P1, P2, .. Pn) in F
       and  names is a list of n names,
       then fmt' is the pretty printed format of P
    *)
(*      fun nameLookup index = List.nth (names, index) *)
(* decName (G, LD) = LD'

           Invariant:
           If   G1 |- LD lfdec
           then LD' = LD modulo new non-conficting variable names.
        *)
let rec decName(g,  , uDec d) uDec (decName (g,  , d)) decName(g,  , pDec (nONE,  , f,  , tC1,  , tC2)) pDec (sOME "xx",  , f,  , tC1,  , tC2) decName(g,  , d) d(*      (* numberOfSplits Ds = n'

           Invariant:
           If   Psi, Delta |- Ds :: Psi', Delta'
           then n'= |Psi'| - |Psi|
        *)
        fun numberOfSplits Ds =
            let
              fun numberOfSplits' (T.Empty, n) = n
                | numberOfSplits' (T.New (_, Ds), n) = numberOfSplits' (Ds, n)
                | numberOfSplits' (T.App (_, Ds), n) = numberOfSplits' (Ds, n)
                | numberOfSplits' (T.Lemma (_, Ds), n) = numberOfSplits' (Ds, n)
                | numberOfSplits' (T.Split (_, Ds), n) = numberOfSplits' (Ds, n+1)
                | numberOfSplits' (T.Left (_, Ds), n) = numberOfSplits' (Ds, n)
                | numberOfSplits' (T.Right (_, Ds), n) = numberOfSplits' (Ds, n)
            in
              numberOfSplits' (Ds, 0)
            end
*)
(* psiName (Psi1, s, Psi2, l) = Psi1'

           Invariant:
           If   |- Psi1 ctx
           and  |- Psi1' ctx
           and  |- Psi2 ctx
           and  Psi2 = Psi2', Psi2''
           and  Psi1 |- s : Psi2
           and  |Psi2''| = l
           then Psi1' = Psi1 modulo variable naming
           and  for all x in Psi2 s.t. s(x) = x in Psi1'
        *)
let rec psiName(psi1,  , s,  , psi2,  , l) let let rec nameDec(d as dec (sOME _,  , _),  , name) d nameDec(dec (nONE,  , v),  , name) dec (sOME name,  , v)let rec namePsi(decl (psi,  , uDec d),  , 1,  , name) decl (psi,  , uDec (nameDec (d,  , name))) namePsi(decl (psi,  , lD as uDec d),  , n,  , name) decl (namePsi (psi,  , n - 1,  , name),  , lD) nameG(psi,  , null,  , n,  , name,  , k) (k n,  , null) nameG(psi,  , decl (g,  , d),  , 1,  , name,  , k) (psi,  , decl (g,  , nameDec (d,  , name))) nameG(psi,  , decl (g,  , d),  , n,  , name,  , k) let let  in in (psi',  , decl (g',  , d))let rec ignore(s,  , 0) s ignore(dot (_,  , s),  , k) ignore (s,  , k - 1) ignore(shift n,  , k) ignore (dot (idx (n + 1),  , shift (n + 1)),  , k - 1)let rec copyNames(shift n,  , g as decl _)psi1 copyNames (dot (idx (n + 1),  , shift (n + 1)),  , g) psi1 copyNames(dot (exp _,  , s),  , decl (g,  , _))psi1 copyNames (s,  , g) psi1 copyNames(dot (idx k,  , s),  , decl (g,  , uDec (dec (nONE,  , _))))psi1 copyNames (s,  , g) psi1 copyNames(dot (idx k,  , s),  , decl (g,  , uDec (dec (sOME name,  , _))))psi1 let let  in in copyNames (s,  , g) psi1' copyNames(dot (prg k,  , s),  , decl (g,  , pDec (nONE,  , _,  , _,  , _)))psi1 copyNames (s,  , g) psi1 copyNames(dot (prg k,  , s),  , decl (g,  , pDec (sOME name,  , _,  , _,  , _)))psi1 copyNames (s,  , g) psi1 copyNames(shift _,  , null)psi1 psi1let rec psiName'(null) null psiName'(decl (psi,  , d)) let let  in in decl (psi',  , decName (coerceCtx psi',  , d)) in psiName' ((* copyNames  (ignore (s, l),  Psi2) *)
psi1)(*

        (* merge (G1, G2) = G'

           Invariant:
           G' = G1, G2
        *)
        fun merge (G1, I.Null) = G1
          | merge (G1, I.Decl (G2, D)) =
              I.Decl (merge (G1, G2), D)

        (* formatCtx (Psi, G) = fmt'

           Invariant:
           If   |- Psi ctx
           and  Psi |- G ctx
           then fmt' is a pretty print format of G
        *)
        fun formatCtx (Psi, G) =
          let
            val G0 = T.makectx Psi

            fun formatCtx' (I.Null) = nil
              | formatCtx' (I.Decl (I.Null, I.Dec (SOME name, V))) =
                  [Fmt.String name, Fmt.String ":",
                   Print.formatExp (G0, V)]
              | formatCtx' (I.Decl (G, I.Dec (SOME name, V))) =
                  (formatCtx' G) @
                  [Fmt.String ",", Fmt.Break,
                   Fmt.String name, Fmt.String ":",
                   Print.formatExp (merge (G0, G), V)]
          in
            Fmt.Hbox (Fmt.String "|" :: (formatCtx' G @ [Fmt.String "|"]))
          end

        (* formatTuple (Psi, P) = fmt'

           Invariant:
           If   |- Psi ctx
           and  Psi; Delta |- P = Inx (M1, Inx ... (Mn, Unit))
           then fmt' is a pretty print format of (M1, .., Mn)
        *)
        fun formatTuple (Psi, P) =
          let
            fun formatTuple' (T.Unit) = nil
              | formatTuple' (T.Inx (M, T.Unit)) =
              [Print.formatExp (T.makectx Psi, M)]
              | formatTuple' (T.Inx (M, P')) =
              (Print.formatExp (T.makectx Psi, M) ::
               Fmt.String "," :: Fmt.Break :: formatTuple' P')
          in
            case P
              of (T.Inx (_, T.Unit)) => Fmt.Hbox (formatTuple' P)
              | _ => Fmt.HVbox0 1 1 1
                (Fmt.String "(" :: (formatTuple' P @ [Fmt.String ")"]))
          end

        (* formatSplitArgs (Psi, L) = fmt'

           Invariant:
           If   |- Psi ctx
           and  L = (M1, .., Mn)
           and  Psi |- Mk:Ak for all 1<=k<=n
           then fmt' is a pretty print format of (M1, .., Mn)
        *)
        fun formatSplitArgs (Psi, L) =
          let
            fun formatSplitArgs' (nil) = nil
              | formatSplitArgs' (M :: nil) =
                  [Print.formatExp (T.makectx Psi, M)]
              | formatSplitArgs' (M :: L) =
                  (Print.formatExp (T.makectx Psi, M) ::
                   Fmt.String "," :: Fmt.Break :: formatSplitArgs' L)
          in
            if List.length L = 1 then Fmt.Hbox (formatSplitArgs' L)
            else Fmt.HVbox0 1 1 1
              (Fmt.String "(" :: (formatSplitArgs' L @ [Fmt.String ")"]))
          end


        (* formatDecs1 (Psi, Ds, s, L) = L'

           Invariant:
           If   |- Psi ctx
           and  Psi; Delta |- Ds : Psi'; Delta'
           and  Psi' = x1:A1 .. xn:An
           and  Psi'' |- s : Psi
           and  for i<=n
                L = (M1 .. Mi)
                s.t   Psi'' |- Mi : Ai
           then L' extends L
           s.t. L = (M1 .. Mn)
                for all i <=n
                Psi'' |- Mi : Ai
                (and Mi is a splitting of a the result of an inductive call)
        *)
        fun formatDecs1 (Psi, T.Split (xx, Ds), I.Dot (Ft, s1), L) =
              formatDecs1 (Psi, Ds, s1, frontToExp (Ft) :: L)
          | formatDecs1 (Psi, T.Empty, s1, L) = L
          | formatDecs1 (Psi, Ds, I.Shift n, L) =
              formatDecs1 (Psi, Ds, I.Dot (I.Idx (n+1), I.Shift (n+1)), L)


        (* formatDecs0 (Psi, Ds) = (Ds', S')

           Invariant:
           If   |- Psi ctx
           and  Psi ; Delta |- Ds : Psi', Delta'
           and  Ds = App M1 ... App Mn Ds'   (where Ds' starts with Split)
           then S' = (M1, M2 .. Mn)
           and  Psi1, Delta1 |- Ds' : Psi1', Delta1'
                (for some Psi1, Delta1, Psi1', Delta1')
        *)
        fun formatDecs0 (Psi, T.App ((xx, M), Ds)) =
            let
              val (Ds', S) =
                formatDecs0 (Psi, Ds)
            in
              (Ds', I.App (M, S))
            end
          | formatDecs0 (Psi, Ds) = (Ds, I.Nil)


        (* formatDecs (index, Psi, Ds, (Psi1, s1)) = fmt'

           Invariant:
           If   |- Psi ctx
           and  Psi; Delta |- Ds : Psi'; Delta'
           and  Psi1 |- s1 : Psi, Psi'
           then fmt' is a pretty print format of Ds
        *)
        fun formatDecs (index, Psi, Ds as T.App ((xx, _), P), (Psi1, s1)) =
            let
              val (Ds', S) = formatDecs0 (Psi, Ds)
              val L' = formatDecs1 (Psi, Ds', s1, nil)
              val name = nameLookup index
            in
              Fmt.Hbox [formatSplitArgs (Psi1, L'), Fmt.Space,
                        Fmt.String "=", Fmt.Break,
                        Fmt.HVbox (Fmt.String name :: Fmt.Break ::
                                   Print.formatSpine callname (T.makectx Psi, S))]
            end
          | formatDecs (index, Psi, T.New (B as T.CtxBlock (_, G), Ds),
                        (Psi1, s1)) =
            let
              val B' = ctxBlockName (T.makectx Psi, B)
              val fmt =
                formatDecs (index, I.Decl (Psi, T.Block B'), Ds, (Psi1, s1))
            in
              Fmt.Vbox [formatCtx (Psi, G), Fmt.Break, fmt]
            end
          | formatDecs (index, Psi, T.Lemma (lemma, Ds), (Psi1, s1)) =
            let
              val (Ds', S) = formatDecs0 (Psi, Ds)
              val L' = formatDecs1 (Psi, Ds', s1, nil)
              val (T.LemmaDec (names, _, _)) = T.lemmaLookup lemma
            in
              Fmt.Hbox [formatSplitArgs (Psi1, L'), Fmt.Space,
                        Fmt.String "=", Fmt.Break,
                        Fmt.HVbox (Fmt.String (List.nth (names, index)) :: Fmt.Break ::
                                   Print.formatSpine callname (T.makectx Psi, S))]
            end
          | formatDecs (index, Psi, T.Left (_, Ds), (Psi1, s1)) =
            let
              val fmt =
                formatDecs (index, Psi, Ds, (Psi1, s1))
            in
              fmt
            end
          | formatDecs (index, Psi, T.Right (_, Ds), (Psi1, s1)) =
            let
              val fmt =
                formatDecs (index+1, Psi, Ds, (Psi1, s1))
            in
              fmt
            end


*)
(* fmtSpine callname (G, d, l, (S, s)) = fmts
     format spine S[s] at printing depth d, printing length l, in printing
     context G which approximates G', where G' |- S[s] is valid
  *)
let rec fmtSpinecallname(psi,  , nil) [] fmtSpinecallname(psi,  , appExp (u,  , s)) hVbox (formatSpine (coerceCtx psi,  , app (u,  , nil))) :: fmtSpine' callname (psi,  , s) fmtSpinecallname(psi,  , appPrg (p,  , s)) formatPrg3 callname (psi,  , p) :: fmtSpine' callname (psi,  , s) fmtSpine'callname(psi,  , nil) [] fmtSpine'callname(psi,  , s) break :: fmtSpine callname (psi,  , s)(*
        (* frontToExp (Ft) = U'

           Invariant:
           G |- Ft = U' : V   for a G, V
        *)
        and frontToExp (T.Idx k) = I.Root (I.BVar k, I.Nil)
          | frontToExp (T.Exp (U)) = U
          | frontToExp (T.Prg (T.PairExp (U, _))) = U    (* this is a patch -cs
                                                            works only with one exists quantifier
                                                            we cannot use LF spines, we need to
                                                            use tomega spines.

                                                            Next step program printer for tomega spines
                                                            Then change this code. *)
*)
(* argsToSpine (Psi1, s, S) = S'

           Invariant:
           If   Psi1 |- s = M1 . M2 .. Mn. ^|Psi1|: Psi2
           and  Psi1 |- S : V1 > {Psi2} V2
           then Psi1 |- S' : V1 > V2
           and S' = S, M1 .. Mn
           where
           then Fmts is a list of arguments
        *)
 argsToSpine(s,  , 0,  , s) s argsToSpine(shift (n),  , k,  , s) argsToSpine (dot (idx (n + 1),  , shift (n + 1)),  , k,  , s) argsToSpine(dot (idx n,  , s),  , k,  , s) argsToSpine (s,  , k - 1,  , appExp (root (bVar n,  , nil),  , s)) argsToSpine(dot (exp (u),  , s),  , k,  , s) argsToSpine (s,  , k - 1,  , appExp (u,  , s)) argsToSpine(dot (prg p,  , s),  , k,  , s) argsToSpine (s,  , k - 1,  , appPrg (p,  , s))(* Idx will always be expanded into Expressions and never into programs
                 is this a problem? -- cs *)
(* formatTuple (Psi, P) = fmt'

           Invariant:
           If   |- Psi ctx
           and  Psi; Delta |- P = Inx (M1, Inx ... (Mn, Unit))
           then fmt' is a pretty print format of (M1, .., Mn)
        *)
 formatTuple(psi,  , p) let let rec formatTuple'(unit) nil formatTuple'(pairExp (m,  , unit)) [formatExp (coerceCtx psi,  , m)] formatTuple'(pairExp (m,  , p')) (formatExp (coerceCtx psi,  , m) :: string "," :: break :: formatTuple' p') in match p with (pairExp (_,  , unit)) -> hbox (formatTuple' p) _ -> hVbox0 1 1 1 (string "(" :: (formatTuple' p @ [string ")"])) formatRedexcallname(psi,  , var k,  , s) let let  inlet  in in hbox [space; hVbox (string name :: break :: fspine)] formatRedexcallname(psi,  , const l,  , s) let let  inlet  in in hbox [space; hVbox (string name :: break :: fspine)] formatRedexcallname(psi,  , (redex (const l,  , _)),  , s) let (* val T.ValDec (name, _, _) = T.lemmaLookup l *)
let  inlet  in in hbox [space; hVbox (string name :: break :: fspine)] formatCasecallname(max,  , psi',  , s,  , psi) let let  inlet  in in hbox [hVbox (fspine)](* formatCases ((max, index), Psi, L) = fmts'

           Invariant:
           If   |- Psi ctx
           and  Psi |- L a list of cases
           then fmts' list of pretty print formats of L
        *)
 formatCases(max,  , psi,  , nil,  , callname) nil formatCases(max,  , psi,  , (psi',  , s,  , p) :: nil,  , callname) let let  inlet  in in [hVbox0 1 5 1 [formatCase callname (max,  , psi'',  , s,  , psi); space; string "="; break; formatPrg3 callname (psi'',  , p)]; break] formatCases(max,  , psi,  , (psi',  , s,  , p) :: o,  , callname) let let  inlet  in in formatCases (max,  , psi,  , o,  , callname) @ [hVbox0 1 5 1 [string "|"; space; formatCase callname (max,  , psi'',  , s,  , psi); space; string "="; break; formatPrg3 callname (psi'',  , p)]; break](* formatPrg3 callname  (Psi, P) = fmt

           Invariant:
           If   |- Psi ctx
           and  Psi; Delta |- P :: F
           and  P = let .. in .. end | <..,..> | <>
           then fmt is a pretty print of P
        *)
 formatPrg3callname(psi,  , unit) string "<>" formatPrg3callname(psi,  , pairExp (u,  , p)) hVbox [string "<"; formatExp (coerceCtx psi,  , u); string ","; break; formatPrg3 callname (psi,  , p); string ">"] formatPrg3callname(psi,  , p as let _) formatLet callname (psi,  , p,  , nil) formatPrg3callname(psi,  , p as letPairExp (d1,  , d2,  , p1,  , p2)) formatLet callname (psi,  , p,  , nil) formatPrg3callname(psi,  , p as letUnit (p1,  , p2)) formatLet callname (psi,  , p,  , nil) formatPrg3callname(psi,  , p as new (lam (uDec (bDec (l,  , (c,  , s))),  , _))) formatNew callname (psi,  , p,  , nil) formatPrg3callname(psi,  , redex (p,  , s)) formatRedex callname (psi,  , p,  , s) formatPrg3callname(psi,  , lam (d as uDec d',  , p)) hVbox [string "lam"; space; string "("; formatDec (coerceCtx psi,  , d'); string ")"; space; formatPrg3 callname (decl (psi,  , d),  , p)] formatPrg3callname(psi,  , rec (d as pDec (sOME name,  , f,  , nONE,  , nONE),  , p)) hVbox [string "fix*"; space; string "("; string name; string ":"; formatFor (psi,  , f); string ")"; space; formatPrg3 callname (decl (psi,  , d),  , p)] formatPrg3callname(psi,  , rec (d as pDec (sOME name,  , f,  , sOME tC1,  , sOME tC2),  , p)) hVbox [string "fix"; space; string "("; string name; string ":"; formatFor (psi,  , f); string ")"; space; formatPrg3 callname (decl (psi,  , d),  , p)] formatPrg3callname(psi,  , pClo (p,  , t)) hVbox [formatPrg3 callname (psi,  , p); string "..."] formatPrg3callname(psi,  , x as eVar (_,  , ref (sOME p),  , _,  , _,  , _,  , _)) formatPrg3 callname (psi,  , p) formatPrg3callname(psi,  , x as eVar (_,  , ref nONE,  , _,  , _,  , _,  , _)) string (nameEVar x) formatPrg3callname(psi,  , case (cases cs)) hVbox (string "case" :: break :: formatCases (1,  , psi,  , cs,  , callname) @ [string "."]) formatPrg3callname(psi,  , var n) let let  in in string n formatPrg3callname_ string "missing case" formatNewcallname(psi,  , new (lam (uDec (d as bDec (l,  , (c,  , s))),  , p)),  , fmts) let let  inlet  in in formatNew callname (decl (psi,  , uDec d'),  , p,  , break :: hVbox [formatDec (g,  , d')] :: fmts) formatNewcallname(psi,  , p,  , fmts) vbox0 0 1 ([string "new"; vbox0 0 1 (fmts); break; string "in"; break; spaces 2; formatPrg3 callname (psi,  , p); break; string "end"])(* formatLet callname (Psi, P, fmts) = fmts'

           Invariant:
           If   |- Psi ctx
           and  Psi; Delta |- P = Let . Case P' :: F
           and  fmts is a list of pretty print formats of P
           then fmts' extends fmts
           and  fmts also includes a pretty print format for P'
        *)
 formatLetcallname(psi,  , let (d,  , p1,  , case (cases ((psi1,  , s1,  , p2 as let _) :: nil))),  , fmts) let let  inlet  inlet  in(* was I.ctxLength Psi - max  --cs *)
(*            val Fspine =   Print.formatSpine callname (T.coerceCtx Psi1, S) *)
let  inlet  inlet  inlet  in in formatLet callname (psi1',  , p2,  , fmts @ [break; fmt]) formatLetcallname(psi,  , let (d,  , p1,  , case (cases ((psi1,  , s1,  , p2) :: nil))),  , fmts) let let  inlet  inlet  in(* was I.ctxLength Psi - max  --cs *)
(*            val Fspine =   Print.formatSpine callname (T.coerceCtx Psi1, S) *)
let  inlet  inlet  inlet  in(*            val fmt = (* formatDecs (0, Psi, Ds, (Psi1', s1)) *)
                Fmt.Hbox [Fmt.String " ..." , Fmt.Space, Fmt.String "=",  Fmt.Break, F1] *)
 in vbox0 0 1 ([string "let"; vbox0 2 1 (fmts @ [break; fmt]); break; string "in"; break; spaces 2; formatPrg3 callname (psi1',  , p2); break; string "end"]) formatLetcallname(psi,  , let (d,  , p1,  , case (cases l)),  , nil) let let rec fmtCaseRest[] [] fmtCaseRest((psi1,  , s1,  , p2) :: l) let let  inlet  inlet  inlet  in in [hVbox [space; string "|"; space; fpattern; space; string "-->"]; spaces 2; vbox0 0 1 [formatPrg3 callname (psi1',  , p2)]; break] @ fmtCaseRest (l)let rec fmtCase((psi1,  , s1,  , p2) :: l) let let  inlet  inlet  inlet  in in vbox0 0 1 ([hVbox [string "of"; space; fpattern; space; string "-->"]; spaces 2; vbox0 0 1 [formatPrg3 callname (psi1',  , p2)]; break] @ fmtCaseRest (l))let  inlet  inlet  in in vbox0 0 1 ([string "case ("; fbody; space(* need space since there is one before Fbody *)
; string ")"; break; fmt]) formatLetcallname(psi,  , r as (let (d,  , p1,  , case (cases l))),  , fmts) vbox0 0 1 ([string "let"; vbox0 0 1 (fmts @ [break]); break; string "in"; break; spaces 2; formatLet callname (psi,  , r,  , nil); break; string "end"]) formatLetcallname(psi,  , r as (let (d as pDec (sOME name,  , f,  , _,  , _),  , p1,  , p2)),  , fmts) vbox0 0 1 ([string "let"; break; vbox0 0 1 ([string name; space; string "="; formatPrg3 callname (psi,  , p1)]); break; string "in"; break; spaces 2; formatPrg3 callname (decl (psi,  , d),  , p2); break; string "end"]) formatLetcallname(psi,  , r as (letPairExp (d1 as dec (sOME n1,  , _),  , d2 as pDec (sOME n2,  , f,  , _,  , _),  , p1,  , p2)),  , fmts) vbox0 0 1 ([string "let"; break; spaces 2; vbox0 0 1 ([string "("; string n1; string ","; space; string n2; string ")"; space; string "="; space; formatPrg3 callname (psi,  , p1)]); break; string "in"; break; spaces 2; formatPrg3 callname (decl (decl (psi,  , uDec d1),  , d2),  , p2); break; string "end"]) formatLetcallname(psi,  , r as (letUnit (p1,  , p2)),  , fmts) vbox0 0 1 ([string "let"; break; spaces 2; vbox0 0 1 ([string "()"; space; string "="; space; formatPrg3 callname (psi,  , p1)]); break; string "in"; break; spaces 2; formatPrg3 callname (psi,  , p2); break; string "end"])(* formatHead callname (index, Psi1, s, Psi2) = fmt'

           Invariant:
           If    Psi1 |- s : Psi2
           then  fmt is a format of the entire head
           where index represents the function name
           and   s the spine.
        *)
 formatHeadcallname(name,  , (max,  , index),  , psi',  , s,  , psi) let (*            val T.PDec (SOME name, _) = I.ctxLookup (Psi, index) *)
let  in(*            val Fspine =   Print.formatSpine callname (T.coerceCtx Psi', S) *)
let  in in hbox [space; hVbox (string name :: break :: fspine)](* formatPrg2 ((max, index), Psi, L) = fmts'

           Invariant:
           If   |- Psi ctx
           and  Psi |- L a list of cases
           then fmts' list of pretty print formats of L
        *)
let rec formatPrg2(name,  , (max,  , index),  , psi,  , nil,  , callname) nil formatPrg2(name,  , (max,  , index),  , psi,  , (psi',  , s,  , p) :: nil,  , callname) let let  inlet  in in [hVbox0 1 5 1 [string fhead; formatHead callname (name,  , (max,  , index),  , psi'',  , s,  , psi); space; string "="; break; formatPrg3 callname (psi'',  , p)]; break] formatPrg2(name,  , (max,  , index),  , psi,  , (psi',  , s,  , p) :: o,  , callname) let let  in in formatPrg2 (name,  , (max,  , index),  , psi,  , o,  , callname) @ [hVbox0 1 5 1 [string "  |"; formatHead callname (name,  , (max,  , index),  , psi'',  , s,  , psi); space; string "="; break; formatPrg3 callname (psi'',  , p)]; break]let rec formatPrg11(name,  , (max,  , index),  , psi,  , lam (d,  , p),  , callname) formatPrg11 (name,  , (max,  , index + 1),  , decl (psi,  , decName (coerceCtx psi,  , d)),  , p,  , callname) formatPrg11(name,  , (max,  , index),  , psi,  , case (cases os),  , callname) formatPrg2 (name,  , (max,  , index),  , psi,  , os,  , callname)(* formatPrg1 ((max, index), Psi, P) = fmts'

           Invariant:
           If   |- Psi ctx
           and  Psi; . |- P :: F
           and  P is either a Lam .. | Case ... | Pair ...
           then fmts' is alist of pretty print formats of P
        *)
let rec formatPrg1(name :: names,  , (max,  , index),  , psi,  , pairPrg (p1,  , p2),  , callname) formatPrg11 (name,  , (max,  , index),  , psi,  , p1,  , callname) @ formatPrg1 (names,  , (max,  , index - 1),  , psi,  , p2,  , callname) formatPrg1([name],  , (max,  , index),  , psi,  , p,  , callname) formatPrg11 (name,  , (max,  , index),  , psi,  , p,  , callname)(* formatPrg0 (Psi, P) = fmt'
           If   |- Psi ctx
           and  Psi; . |- P :: F
           then fmt' is a pretty print format of P
        *)
(*      fun formatPrg0 (T.Rec (T.PDec (SOME _, F),
                             T.Case (T.Cases [(Psi, t, P)]))) =
          let
            val max = I.ctxLength Psi   (* number of ih. *)
          in
            Fmt.Vbox0 0 1 (formatPrg1 ((max, max), Psi, P))
          end
*)
let rec lookup(name :: names,  , proj :: projs)lemma if lemma = proj then name else lookup (names,  , projs) lemmalet rec formatPrg0((names,  , projs),  , rec (d as pDec (sOME _,  , f,  , _,  , _),  , p)) let let  in(* number of ih. *)
 in vbox0 0 1 (formatPrg1 (names,  , (max,  , max),  , decl (null,  , d),  , p,  , fun lemma -> lookup (names,  , projs) lemma))let rec formatFunargs (varReset null; formatPrg0 args)(*    fun formatLemmaDec (T.LemmaDec (names, P, F)) =
      Fmt.Vbox0 0 1 [formatFor (I.Null, F) names, Fmt.Break,
                     formatPrg (I.Null, P) names]
*)
let rec funToStringargs makestring_fmt (formatFun args)let rec prgToStringargs makestring_fmt (formatPrg3 (fun _ -> "?") args)(*   fun lemmaDecToString Args = Fmt.makestring_fmt (formatLemmaDec Args) *)
(*    fun prgToString Args names = "not yet implemented " *)
let rec nameCtxnull null nameCtx(decl (psi,  , uDec d)) decl (nameCtx psi,  , uDec (decName (coerceCtx psi,  , d))) nameCtx(decl (psi,  , pDec (nONE,  , f,  , tC1,  , tC2))) let let  inlet  in in decl (psi',  , pDec (x,  , f,  , tC1,  , tC2)) nameCtx(decl (psi,  , d as pDec (sOME n,  , f,  , _,  , _))) decl (nameCtx psi,  , d)let rec flagnONE "" flag(sOME _) "*"(* formatCtx (Psi) = fmt'

       Invariant:
       If   |- Psi ctx       and Psi is already named
       then fmt' is a format describing the context Psi
    *)
let rec formatCtx(null) [] formatCtx(decl (null,  , uDec d)) if ! chatter >= 4 then [hVbox ([break; formatDec (null,  , d)])] else [formatDec (null,  , d)] formatCtx(decl (null,  , pDec (sOME s,  , f,  , tC1,  , tC2))) if ! chatter >= 4 then [hVbox ([break; string s; space; string ("::" ^ flag tC1); space; formatFor (null,  , f)])] else [string s; space; string ("::" ^ flag tC1); space; formatFor (null,  , f)] formatCtx(decl (psi,  , uDec d)) let let  in in if ! chatter >= 4 then formatCtx psi @ [string ","; break; break] @ [hVbox ([break; formatDec (g,  , d)])] else formatCtx psi @ [string ","; break] @ [break; formatDec (g,  , d)] formatCtx(decl (psi,  , pDec (sOME s,  , f,  , tC1,  , tC2))) if ! chatter >= 4 then formatCtx psi @ [string ","; break; break] @ [hVbox ([break; string s; space; string ("::" ^ flag tC1); space; formatFor (psi,  , f)])] else formatCtx psi @ [string ","; break] @ [break; string s; space; string ("::" ^ flag tC1); space; formatFor (psi,  , f)]let rec ctxToStringpsi makestring_fmt (hVbox (formatCtx psi))let  inlet  inlet  inlet  in(*    val formatLemmaDec = formatLemmaDec *)
let  inlet  inlet  inlet  inlet  inlet  inlet  inlet  in(*    val lemmaDecToString = lemmaDecToString *)
end