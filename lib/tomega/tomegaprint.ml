(* Printing of functional proof terms *)
(* Author: Carsten Schuermann *)

functor (* GEN BEGIN FUNCTOR DECL *) TomegaPrint
  ((*! structure IntSyn' : INTSYN !*)
   (*! structure Tomega' : TOMEGA !*)
   (*! sharing Tomega'.IntSyn = IntSyn' !*)
(*   structure Normalize : NORMALIZE *)
   (*! sharing Normalize.IntSyn = IntSyn' !*)
   (*! sharing Normalize.Tomega = Tomega' !*)
   structure Formatter : FORMATTER
   structure Names : NAMES
   (*! sharing Names.IntSyn = IntSyn' !*)
   structure Print : PRINT
     sharing Print.Formatter = Formatter
     (*! sharing Print.IntSyn = IntSyn' !*)
       )
  : TOMEGAPRINT =

struct
  (*! structure IntSyn = IntSyn' !*)
  (*! structure Tomega = Tomega' !*)
  structure Formatter = Formatter

    exception Error of string
    (* is just here because we don't have a
     module yet for names. move later
     --cs Tue Apr 27 12:04:45 2004 *)

  local
    structure I = IntSyn
    structure T = Tomega
    structure Fmt = Formatter
    structure P = Print

    (* Invariant:

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


    (* GEN BEGIN TAG OUTSIDE LET *) val evarList : (T.prg) list ref = ref nil (* GEN END TAG OUTSIDE LET *)

    fun evarReset () = (evarList := nil)

    fun evarName n =
      let
    
        fun (* GEN BEGIN FUN FIRST *) evarName' nil = raise Error "not found" (* GEN END FUN FIRST *)
          | (* GEN BEGIN FUN BRANCH *) evarName' ((Y as T.EVar (_, _, _, _, _, X as I.EVar (_, G, r, _))) :: L) =
            if Names.evarName (G, X) = n then Y else evarName' L (* GEN END FUN BRANCH *)
      in
        evarName' (!evarList)
      end

    fun nameEVar (T.EVar (_, _, _, _, _, X as I.EVar (_, G, r, _))) = Names.evarName (G, X)

    (* formatCtxBlock (G, (G1, s1)) = (G', s', fmts')

       Invariant:
       If   |- G ctx
       and  G |- G1 ctx
       and  G2 |- s1 : G
       then G' = G2, G1 [s1]
       and  G' |- s' : G, G1
       and  fmts is a format list of G1[s1]
    *)
    fun (* GEN BEGIN FUN FIRST *) formatCtxBlock (G, (I.Null, s)) = (G, s, nil) (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) formatCtxBlock (G, (I.Decl (I.Null, D), s)) =
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val D' = I.decSub (D, s) (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val fmt = P.formatDec (G, D') (* GEN END TAG OUTSIDE LET *)
        in
          (I.Decl (G, D'), I.dot1 s, [fmt])
        end (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) formatCtxBlock (G, (I.Decl (G', D), s)) =
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val (G'', s'', fmts) = formatCtxBlock (G, (G', s)) (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val D'' = I.decSub (D, s'') (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val fmt = P.formatDec (G'', D'') (* GEN END TAG OUTSIDE LET *)
        in
          (I.Decl (G'', D''), I.dot1 s'', fmts @
           [Fmt.String ",", Fmt.Break, fmt])
        end (* GEN END FUN BRANCH *)


    fun constName c = I.conDecName (I.sgnLookup c)

    fun (* GEN BEGIN FUN FIRST *) formatWorld nil = [] (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) formatWorld [c] = [Fmt.String (constName c)] (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) formatWorld (c :: cids) = [Fmt.String (constName c), Fmt.String ",", Fmt.Break] @ formatWorld cids (* GEN END FUN BRANCH *)

    (* formatFor' (G, (F, s)) = fmts'

       Invariant:
       If   |- G ctx
       and  G |- s : Psi'
       and  Psi' |- F formula
       then fmts' is a list of formats for F
    *)
    fun (* GEN BEGIN FUN FIRST *) formatFor' (Psi, T.All ((D, T.Explicit), F)) =
        (case D
           of T.UDec D =>
             let
               (* GEN BEGIN TAG OUTSIDE LET *) val G = T.coerceCtx Psi (* GEN END TAG OUTSIDE LET *)
               (* GEN BEGIN TAG OUTSIDE LET *) val D' = Names.decName (G, D) (* GEN END TAG OUTSIDE LET *)
             in
               [Fmt.String "all {", P.formatDec (G, D'),
                Fmt.String "}", Fmt.Break] @
               formatFor' (I.Decl (Psi, T.UDec D'), F)
             end) (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) formatFor' (Psi, T.All ((D, T.Implicit), F)) =
        (case D
           of T.UDec D =>
             let
               (* GEN BEGIN TAG OUTSIDE LET *) val G = T.coerceCtx Psi (* GEN END TAG OUTSIDE LET *)
               (* GEN BEGIN TAG OUTSIDE LET *) val D' = Names.decName (G, D) (* GEN END TAG OUTSIDE LET *)
             in
               [Fmt.String "all^ {", P.formatDec (G, D'),
                Fmt.String "}", Fmt.Break] @
               formatFor' (I.Decl (Psi, T.UDec D'), F)
             end) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) formatFor' (Psi, T.Ex ((D, T.Explicit), F)) =
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val G = T.coerceCtx Psi (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val D' = Names.decName (G, D) (* GEN END TAG OUTSIDE LET *)
        in
          [Fmt.String "exists {", P.formatDec (G,  D'), Fmt.String "}", Fmt.Break] @
          formatFor' (I.Decl (Psi, T.UDec D'), F)
        end (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) formatFor' (Psi, T.Ex ((D, T.Implicit), F)) =
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val G = T.coerceCtx Psi (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val D' = Names.decName (G, D) (* GEN END TAG OUTSIDE LET *)
        in
          [Fmt.String "exists^ {", P.formatDec (G,  D'), Fmt.String "}", Fmt.Break] @
          formatFor' (I.Decl (Psi, T.UDec D'), F)
        end (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) formatFor' (Psi, T.And (F1, F2)) =
          [Fmt.String "(",
           Fmt.HVbox (formatFor' (Psi, F1)),
           Fmt.String ")", Fmt.Break, Fmt.String "/\\", Fmt.Space, Fmt.String "(",
           Fmt.HVbox (formatFor' (Psi, F2)),
           Fmt.String ")"] (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) formatFor' (Psi, T.True) =
        [Fmt.String "true"] (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) formatFor' (Psi, T.World (T.Worlds L, F)) =
          [Fmt.String "world (", Fmt.HVbox (formatWorld L), Fmt.String ")", Fmt.Break] @
          formatFor' (Psi, F) (* GEN END FUN BRANCH *)



    fun formatFor (G, F) = Fmt.HVbox (formatFor' (G, T.forSub (F, T.id)))
    fun forToString (Psi, F) = Fmt.makestring_fmt (formatFor (Psi, F))


    (* formatPrg (Psi, P) names = fmt'

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
        fun (* GEN BEGIN FUN FIRST *) decName (G, T.UDec D) =  T.UDec (Names.decName (G, D)) (* GEN END FUN FIRST *)
          | (* GEN BEGIN FUN BRANCH *) decName (G, T.PDec (NONE, F, TC1, TC2))= T.PDec (SOME "xx", F, TC1, TC2) (* GEN END FUN BRANCH *)
               (* needs to be integrated with Names *)
          | (* GEN BEGIN FUN BRANCH *) decName (G, D) = D (* GEN END FUN BRANCH *)


(*      (* numberOfSplits Ds = n'

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
        fun psiName (Psi1, s, Psi2, l) =
          let
            fun (* GEN BEGIN FUN FIRST *) nameDec (D as I.Dec (SOME _, _), name) = D (* GEN END FUN FIRST *)
              | (* GEN BEGIN FUN BRANCH *) nameDec (I.Dec (NONE, V), name) = I.Dec (SOME name, V) (* GEN END FUN BRANCH *)
        
            fun (* GEN BEGIN FUN FIRST *) namePsi (I.Decl (Psi, T.UDec D), 1, name) =
                  I.Decl (Psi, T.UDec (nameDec (D, name))) (* GEN END FUN FIRST *)
              | (* GEN BEGIN FUN BRANCH *) namePsi (I.Decl (Psi, LD as T.UDec D), n, name) =
                  I.Decl (namePsi (Psi, n-1, name), LD) (* GEN END FUN BRANCH *)
            and (* GEN BEGIN FUN FIRST *) nameG (Psi, I.Null, n, name, k) = (k n, I.Null) (* GEN END FUN FIRST *)
              | (* GEN BEGIN FUN BRANCH *) nameG (Psi, I.Decl (G, D), 1, name, k) = (Psi, I.Decl (G, nameDec (D, name))) (* GEN END FUN BRANCH *)
              | (* GEN BEGIN FUN BRANCH *) nameG (Psi, I.Decl (G, D), n, name, k) =
                let
                  (* GEN BEGIN TAG OUTSIDE LET *) val (Psi', G') = nameG (Psi, G, n-1, name, k) (* GEN END TAG OUTSIDE LET *)
                in
                  (Psi', I.Decl (G', D))
                end (* GEN END FUN BRANCH *)
        
        
            fun (* GEN BEGIN FUN FIRST *) ignore (s, 0) = s (* GEN END FUN FIRST *)
              | (* GEN BEGIN FUN BRANCH *) ignore (T.Dot (_, s), k) = ignore (s, k-1) (* GEN END FUN BRANCH *)
              | (* GEN BEGIN FUN BRANCH *) ignore (T.Shift n, k) =
                  ignore (T.Dot (T.Idx (n+1), T.Shift (n+1)), k-1) (* GEN END FUN BRANCH *)
        
            fun (* GEN BEGIN FUN FIRST *) copyNames (T.Shift n, G as I.Decl _) Psi1=
                  copyNames (T.Dot (T.Idx (n+1), T.Shift (n+1)), G) Psi1 (* GEN END FUN FIRST *)
              | (* GEN BEGIN FUN BRANCH *) copyNames (T.Dot (T.Exp _, s), I.Decl (G, _)) Psi1=
                  copyNames (s, G) Psi1 (* GEN END FUN BRANCH *)
              | (* GEN BEGIN FUN BRANCH *) copyNames (T.Dot (T.Idx k, s), I.Decl (G, T.UDec (I.Dec (NONE, _)))) Psi1 =
                  copyNames (s, G) Psi1 (* GEN END FUN BRANCH *)
              | (* GEN BEGIN FUN BRANCH *) copyNames (T.Dot (T.Idx k, s), I.Decl (G, T.UDec (I.Dec (SOME name, _)))) Psi1 =
                let
                  (* GEN BEGIN TAG OUTSIDE LET *) val Psi1' = namePsi (Psi1, k, name) (* GEN END TAG OUTSIDE LET *)
                in
                  copyNames (s, G) Psi1'
                end (* GEN END FUN BRANCH *)
              | (* GEN BEGIN FUN BRANCH *) copyNames (T.Dot (T.Prg k, s), I.Decl (G, T.PDec (NONE, _, _, _))) Psi1 =
                  copyNames (s, G) Psi1 (* GEN END FUN BRANCH *)
              | (* GEN BEGIN FUN BRANCH *) copyNames (T.Dot (T.Prg k, s), I.Decl (G, T.PDec (SOME name, _, _, _))) Psi1 =
                  copyNames (s, G) Psi1 (* GEN END FUN BRANCH *)
        
        
              | (* GEN BEGIN FUN BRANCH *) copyNames (T.Shift _, I.Null) Psi1 = Psi1 (* GEN END FUN BRANCH *)
        
            fun (* GEN BEGIN FUN FIRST *) psiName' (I.Null) = I.Null (* GEN END FUN FIRST *)
              | (* GEN BEGIN FUN BRANCH *) psiName' (I.Decl (Psi, D)) =
                let
                  (* GEN BEGIN TAG OUTSIDE LET *) val Psi' = psiName' Psi (* GEN END TAG OUTSIDE LET *)
                in
                  I.Decl (Psi', decName (T.coerceCtx Psi', D))
                end (* GEN END FUN BRANCH *)
          in
            psiName' ((* copyNames  (ignore (s, l),  Psi2) *) Psi1)
          end
(*

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
  fun (* GEN BEGIN FUN FIRST *) fmtSpine callname (Psi,  T.Nil) = [] (* GEN END FUN FIRST *)
    | (* GEN BEGIN FUN BRANCH *) fmtSpine callname (Psi, T.AppExp (U, S)) =
         (* Print.formatExp (T.coerceCtx Psi, U) *)
         Fmt.HVbox (Print.formatSpine (T.coerceCtx Psi, I.App (U, I.Nil)))
         :: fmtSpine' callname (Psi, S) (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) fmtSpine callname (Psi, T.AppPrg (P, S)) =
         formatPrg3 callname  (Psi, P)
         :: fmtSpine' callname (Psi, S) (* GEN END FUN BRANCH *)

  and (* GEN BEGIN FUN FIRST *) fmtSpine' callname (Psi, T.Nil) = [] (* GEN END FUN FIRST *)
    | (* GEN BEGIN FUN BRANCH *) fmtSpine' callname (Psi, S) =
        Fmt.Break :: fmtSpine callname (Psi, S) (* GEN END FUN BRANCH *)



(*
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
        and (* GEN BEGIN FUN FIRST *) argsToSpine (s, 0, S) = S (* GEN END FUN FIRST *)
          | (* GEN BEGIN FUN BRANCH *) argsToSpine (T.Shift (n), k, S) =
              argsToSpine (T.Dot (T.Idx (n+1), T.Shift (n+1)), k, S) (* GEN END FUN BRANCH *)
          | (* GEN BEGIN FUN BRANCH *) argsToSpine (T.Dot (T.Idx n, s), k, S) =
              argsToSpine (s, k-1, T.AppExp (I.Root (I.BVar n, I.Nil), S)) (* GEN END FUN BRANCH *)
          | (* GEN BEGIN FUN BRANCH *) argsToSpine (T.Dot (T.Exp (U), s), k, S) =
              argsToSpine (s, k-1, T.AppExp (U, S)) (* GEN END FUN BRANCH *)
          | (* GEN BEGIN FUN BRANCH *) argsToSpine (T.Dot (T.Prg P, s), k, S) =
              argsToSpine (s, k-1, T.AppPrg (P, S)) (* GEN END FUN BRANCH *)

              (* Idx will always be expanded into Expressions and never into programs
                 is this a problem? -- cs *)


        (* formatTuple (Psi, P) = fmt'

           Invariant:
           If   |- Psi ctx
           and  Psi; Delta |- P = Inx (M1, Inx ... (Mn, Unit))
           then fmt' is a pretty print format of (M1, .., Mn)
        *)
        and formatTuple (Psi, P) =
          let
            fun (* GEN BEGIN FUN FIRST *) formatTuple' (T.Unit) = nil (* GEN END FUN FIRST *)
              | (* GEN BEGIN FUN BRANCH *) formatTuple' (T.PairExp (M, T.Unit)) =
              [Print.formatExp (T.coerceCtx Psi, M)] (* GEN END FUN BRANCH *)
              | (* GEN BEGIN FUN BRANCH *) formatTuple' (T.PairExp (M, P')) =
              (Print.formatExp (T.coerceCtx Psi, M) ::
               Fmt.String "," :: Fmt.Break :: formatTuple' P') (* GEN END FUN BRANCH *)
          in
            case P
              of (T.PairExp (_, T.Unit)) => Fmt.Hbox (formatTuple' P)
              | _ => Fmt.HVbox0 1 1 1
                (Fmt.String "(" :: (formatTuple' P @ [Fmt.String ")"]))
          end


        and (* GEN BEGIN FUN FIRST *) formatRedex callname (Psi, T.Var k, S) =
            (* no mutual recursion, recursive call *)
            let
              (* GEN BEGIN TAG OUTSIDE LET *) val T.PDec (SOME name, _, _, _) = I.ctxLookup (Psi, k) (* GEN END TAG OUTSIDE LET *)
              (* GEN BEGIN TAG OUTSIDE LET *) val Fspine = fmtSpine callname (Psi, S) (* GEN END TAG OUTSIDE LET *)
            in
              Fmt.Hbox [Fmt.Space,
                        Fmt.HVbox (Fmt.String name :: Fmt.Break  :: Fspine)]
            end (* GEN END FUN FIRST *)
          | (* GEN BEGIN FUN BRANCH *) formatRedex callname (Psi, T.Const l, S) =
            (* lemma application *)
            let
              (* GEN BEGIN TAG OUTSIDE LET *) val T.ValDec (name, _, _) = T.lemmaLookup l (* GEN END TAG OUTSIDE LET *)
              (* GEN BEGIN TAG OUTSIDE LET *) val Fspine = fmtSpine callname (Psi, S) (* GEN END TAG OUTSIDE LET *)
            in
              Fmt.Hbox [Fmt.Space,
                        Fmt.HVbox (Fmt.String name :: Fmt.Break  :: Fspine)]
            end (* GEN END FUN BRANCH *)
          | (* GEN BEGIN FUN BRANCH *) formatRedex callname (Psi, (T.Redex (T.Const l, _)), S) =
            (* mutual recursion, k is the projection function *)
            let
              (* val T.ValDec (name, _, _) = T.lemmaLookup l *)
              (* GEN BEGIN TAG OUTSIDE LET *) val name = callname l (* GEN END TAG OUTSIDE LET *)
              (* GEN BEGIN TAG OUTSIDE LET *) val Fspine = fmtSpine callname (Psi, S) (* GEN END TAG OUTSIDE LET *)
            in
              Fmt.Hbox [Fmt.Space,
                        Fmt.HVbox (Fmt.String name :: Fmt.Break  :: Fspine)]
            end (* GEN END FUN BRANCH *)


        and formatCase callname (max, Psi', s, Psi) =
            let
              (* GEN BEGIN TAG OUTSIDE LET *) val S = argsToSpine (s, I.ctxLength Psi - max, T.Nil) (* GEN END TAG OUTSIDE LET *)
              (* GEN BEGIN TAG OUTSIDE LET *) val Fspine = fmtSpine callname (Psi', S) (* GEN END TAG OUTSIDE LET *)
            in
              Fmt.Hbox [Fmt.HVbox (Fspine)]
            end


        (* formatCases ((max, index), Psi, L) = fmts'

           Invariant:
           If   |- Psi ctx
           and  Psi |- L a list of cases
           then fmts' list of pretty print formats of L
        *)
        and (* GEN BEGIN FUN FIRST *) formatCases (max, Psi, nil, callname) = nil (* GEN END FUN FIRST *)
          | (* GEN BEGIN FUN BRANCH *) formatCases (max, Psi, (Psi', s, P) :: nil, callname) =
            let
              (* GEN BEGIN TAG OUTSIDE LET *) val Psi'' = psiName (Psi', s, Psi, 0) (* GEN END TAG OUTSIDE LET *)
              (* GEN BEGIN TAG OUTSIDE LET *) val _ = Names.varReset I.Null (* GEN END TAG OUTSIDE LET *)
            in
              [Fmt.HVbox0 1 5 1
               [formatCase callname (max, Psi'', s, Psi),
                Fmt.Space, Fmt.String "=",  Fmt.Break,
                formatPrg3 callname  (Psi'', P)], Fmt.Break]
            end (* GEN END FUN BRANCH *)
          | (* GEN BEGIN FUN BRANCH *) formatCases (max, Psi, (Psi', s, P) :: O, callname) =
            let
              (* GEN BEGIN TAG OUTSIDE LET *) val
                Psi'' = psiName (Psi', s, Psi, 0) (* GEN END TAG OUTSIDE LET *)
              (* GEN BEGIN TAG OUTSIDE LET *) val _ = Names.varReset I.Null (* GEN END TAG OUTSIDE LET *)
            in
              formatCases (max, Psi, O, callname) @
              [Fmt.HVbox0 1 5 1
               [Fmt.String "|", Fmt.Space, formatCase callname (max, Psi'', s, Psi),
                Fmt.Space, Fmt.String "=", Fmt.Break,
                formatPrg3 callname  (Psi'', P)], Fmt.Break]
            end (* GEN END FUN BRANCH *)


        (* formatPrg3 callname  (Psi, P) = fmt

           Invariant:
           If   |- Psi ctx
           and  Psi; Delta |- P :: F
           and  P = let .. in .. end | <..,..> | <>
           then fmt is a pretty print of P
        *)
        and (* GEN BEGIN FUN FIRST *) formatPrg3 callname  (Psi, T.Unit) = Fmt.String "<>" (* GEN END FUN FIRST *)  (* formatTuple (Psi, P) *)
          | (* GEN BEGIN FUN BRANCH *) formatPrg3 callname  (Psi, T.PairExp (U, P)) =
              Fmt.HVbox [Fmt.String "<", Print.formatExp (T.coerceCtx Psi, U),
                         Fmt.String ",", Fmt.Break, formatPrg3 callname  (Psi, P), Fmt.String ">"] (* GEN END FUN BRANCH *)
(* formatTuple (Psi, P) *)
          | (* GEN BEGIN FUN BRANCH *) formatPrg3 callname  (Psi, P as T.Let _) = formatLet callname (Psi, P, nil) (* GEN END FUN BRANCH *)
          | (* GEN BEGIN FUN BRANCH *) formatPrg3 callname  (Psi, P as T.LetPairExp (D1, D2, P1, P2)) = formatLet callname (Psi, P, nil) (* GEN END FUN BRANCH *)
          | (* GEN BEGIN FUN BRANCH *) formatPrg3 callname  (Psi, P as T.LetUnit (P1, P2)) = formatLet callname (Psi, P, nil) (* GEN END FUN BRANCH *)
          | (* GEN BEGIN FUN BRANCH *) formatPrg3 callname  (Psi, P as T.New (T.Lam (T.UDec (I.BDec (l, (c, s))), _))) =
              formatNew callname (Psi, P, nil) (* GEN END FUN BRANCH *)
          | (* GEN BEGIN FUN BRANCH *) formatPrg3 callname  (Psi, T.Redex (P, S)) =  formatRedex callname (Psi, P, S) (* GEN END FUN BRANCH *)
          | (* GEN BEGIN FUN BRANCH *) formatPrg3 callname  (Psi, T.Lam (D as T.UDec D', P)) =
              Fmt.HVbox [Fmt.String "lam", Fmt.Space, Fmt.String "(",
                         Print.formatDec (T.coerceCtx Psi, D'), Fmt.String ")", Fmt.Space,
                         formatPrg3 callname (I.Decl (Psi, D), P)] (* GEN END FUN BRANCH *)
          | (* GEN BEGIN FUN BRANCH *) formatPrg3 callname  (Psi, T.Rec (D as T.PDec (SOME name, F, NONE, NONE), P)) =
              Fmt.HVbox [Fmt.String "fix*", Fmt.Space, Fmt.String "(",
                         Fmt.String name, Fmt.String ":", formatFor (Psi, F), Fmt.String ")", Fmt.Space,
                         formatPrg3 callname (I.Decl (Psi, D), P)] (* GEN END FUN BRANCH *)
          | (* GEN BEGIN FUN BRANCH *) formatPrg3 callname  (Psi, T.Rec (D as T.PDec (SOME name, F, SOME TC1, SOME TC2), P)) =
              Fmt.HVbox [Fmt.String "fix", Fmt.Space, Fmt.String "(",
                         Fmt.String name, Fmt.String ":", formatFor (Psi, F), Fmt.String ")", Fmt.Space,
                         formatPrg3 callname (I.Decl (Psi, D), P)] (* GEN END FUN BRANCH *)
          | (* GEN BEGIN FUN BRANCH *) formatPrg3 callname (Psi, T.PClo (P, t)) =
              Fmt.HVbox [formatPrg3 callname (Psi, P), Fmt.String "..."] (* GEN END FUN BRANCH *)
          | (* GEN BEGIN FUN BRANCH *) formatPrg3 callname (Psi, X as T.EVar (_, ref (SOME P), _, _, _, _)) = formatPrg3 callname (Psi, P) (* GEN END FUN BRANCH *)
          | (* GEN BEGIN FUN BRANCH *) formatPrg3 callname (Psi, X as T.EVar (_, ref NONE, _, _, _, _)) =
              Fmt.String (nameEVar X) (* GEN END FUN BRANCH *)
          | (* GEN BEGIN FUN BRANCH *) formatPrg3 callname (Psi, T.Case (T.Cases Cs)) =
              Fmt.HVbox (Fmt.String "case" :: Fmt.Break
                         :: formatCases (1, Psi, Cs, callname) @ [Fmt.String "."]) (* GEN END FUN BRANCH *)
          (* need to fix the first  argument to formatcases Tue Apr 27 10:38:57 2004 --cs *)
          | (* GEN BEGIN FUN BRANCH *) formatPrg3 callname  (Psi, T.Var n) =
              let
                (* GEN BEGIN TAG OUTSIDE LET *) val T.PDec (SOME n, _, _, _) = I.ctxLookup (Psi,n) (* GEN END TAG OUTSIDE LET *)
              in
                Fmt.String n
              end (* GEN END FUN BRANCH *)
          | (* GEN BEGIN FUN BRANCH *) formatPrg3 callname  _ = Fmt.String "missing case" (* GEN END FUN BRANCH *)


        and (* GEN BEGIN FUN FIRST *) formatNew callname (Psi, T.New (T.Lam (T.UDec (D as I.BDec (l, (c, s))), P)), fmts) =
            let
              (* GEN BEGIN TAG OUTSIDE LET *) val G = T.coerceCtx Psi (* GEN END TAG OUTSIDE LET *)
              (* GEN BEGIN TAG OUTSIDE LET *) val D' = Names.decName (G, D) (* GEN END TAG OUTSIDE LET *)
            in
              formatNew callname (I.Decl (Psi, T.UDec D'), P,
                         Fmt.Break :: Fmt.HVbox [Print.formatDec (G, D')]
                         ::  fmts)
            end (* GEN END FUN FIRST *)
          | (* GEN BEGIN FUN BRANCH *) formatNew callname (Psi, P, fmts) =
              Fmt.Vbox0 0 1 ([Fmt.String "new",
                              Fmt.Vbox0 0 1 (fmts),
                              Fmt.Break,
                              Fmt.String "in", Fmt.Break,
                              Fmt.Spaces 2, formatPrg3 callname  (Psi, P),
                              Fmt.Break,
                              Fmt.String "end"]) (* GEN END FUN BRANCH *)


        (* formatLet callname (Psi, P, fmts) = fmts'

           Invariant:
           If   |- Psi ctx
           and  Psi; Delta |- P = Let . Case P' :: F
           and  fmts is a list of pretty print formats of P
           then fmts' extends fmts
           and  fmts also includes a pretty print format for P'
        *)
        and (* GEN BEGIN FUN FIRST *) formatLet callname (Psi, T.Let (D, P1, T.Case (T.Cases
                                ((Psi1, s1, P2 as T.Let _) ::  nil))), fmts) =
            let
              (* GEN BEGIN TAG OUTSIDE LET *) val Psi1' = psiName (Psi1, s1, Psi, 1) (* GEN END TAG OUTSIDE LET *)
              (* GEN BEGIN TAG OUTSIDE LET *) val F1 = Fmt.HVbox [formatPrg3 callname  (Psi, P1)] (* GEN END TAG OUTSIDE LET *)
        
              (* GEN BEGIN TAG OUTSIDE LET *) val S = argsToSpine (s1, 1, T.Nil) (* GEN END TAG OUTSIDE LET *)   (* was I.ctxLength Psi - max  --cs *)
        (*            val Fspine =   Print.formatSpine callname (T.coerceCtx Psi1, S) *)
              (* GEN BEGIN TAG OUTSIDE LET *) val Fspine = fmtSpine callname (Psi1, S) (* GEN END TAG OUTSIDE LET *)
        
              (* GEN BEGIN TAG OUTSIDE LET *) val Fpattern =  Fmt.HVbox [Fmt.Hbox (Fspine)] (* GEN END TAG OUTSIDE LET *)
              (* GEN BEGIN TAG OUTSIDE LET *) val Fbody = Fmt.HVbox [F1] (* GEN END TAG OUTSIDE LET *)
              (* GEN BEGIN TAG OUTSIDE LET *) val fmt = Fmt.HVbox [Fmt.HVbox  [Fmt.String "val", Fmt.Space, Fpattern, Fmt.Space, Fmt.String "="], Fmt.Break, Fbody] (* GEN END TAG OUTSIDE LET *)
            in
              formatLet callname (Psi1', P2, fmts @ [Fmt.Break, fmt])
            end (* GEN END FUN FIRST *)
          | (* GEN BEGIN FUN BRANCH *) formatLet callname (Psi, T.Let (D, P1, T.Case (T.Cases
                                ((Psi1, s1, P2) ::  nil))), fmts) =
            let
              (* GEN BEGIN TAG OUTSIDE LET *) val Psi1' = psiName (Psi1, s1, Psi, 1) (* GEN END TAG OUTSIDE LET *)
              (* GEN BEGIN TAG OUTSIDE LET *) val F1 = Fmt.HVbox [formatPrg3 callname  (Psi, P1)] (* GEN END TAG OUTSIDE LET *)
          
              (* GEN BEGIN TAG OUTSIDE LET *) val S = argsToSpine (s1, 1, T.Nil) (* GEN END TAG OUTSIDE LET *)   (* was I.ctxLength Psi - max  --cs *)
          (*            val Fspine =   Print.formatSpine callname (T.coerceCtx Psi1, S) *)
              (* GEN BEGIN TAG OUTSIDE LET *) val Fspine = fmtSpine callname (Psi1, S) (* GEN END TAG OUTSIDE LET *)
          
              (* GEN BEGIN TAG OUTSIDE LET *) val Fpattern =  Fmt.HVbox [Fmt.Hbox (Fspine)] (* GEN END TAG OUTSIDE LET *)
              (* GEN BEGIN TAG OUTSIDE LET *) val Fbody = Fmt.HVbox [F1] (* GEN END TAG OUTSIDE LET *)
              (* GEN BEGIN TAG OUTSIDE LET *) val fmt = Fmt.HVbox [Fmt.HVbox  [Fmt.String "val", Fmt.Space, Fpattern, Fmt.Space, Fmt.String "="], Fmt.Break, Fbody] (* GEN END TAG OUTSIDE LET *)
          
          (*            val fmt = (* formatDecs (0, Psi, Ds, (Psi1', s1)) *)
                Fmt.Hbox [Fmt.String " ..." , Fmt.Space, Fmt.String "=",  Fmt.Break, F1] *)
            in
              Fmt.Vbox0 0 1 ([Fmt.String "let",
                              Fmt.Vbox0 2 1 (fmts @ [Fmt.Break, fmt]),
                              Fmt.Break,
                              Fmt.String "in", Fmt.Break,
                              Fmt.Spaces 2, formatPrg3 callname  (Psi1', P2),
                              Fmt.Break,
                              Fmt.String "end"])
            end (* GEN END FUN BRANCH *)


          (* Added by ABP -- 2/25/03 -- Now a let can have multiple cases *)

          | (* GEN BEGIN FUN BRANCH *) formatLet callname (Psi, T.Let (D, P1, T.Case (T.Cases L)), nil) =
            let
          
              fun (* GEN BEGIN FUN FIRST *) fmtCaseRest [] = [] (* GEN END FUN FIRST *)
                | (* GEN BEGIN FUN BRANCH *) fmtCaseRest ((Psi1, s1, P2)::L) =
                let
                  (* GEN BEGIN TAG OUTSIDE LET *) val Psi1' = psiName (Psi1, s1, Psi, 1) (* GEN END TAG OUTSIDE LET *)
                  (* GEN BEGIN TAG OUTSIDE LET *) val S = argsToSpine (s1, 1, T.Nil) (* GEN END TAG OUTSIDE LET *)
                  (* GEN BEGIN TAG OUTSIDE LET *) val Fspine = fmtSpine callname (Psi1, S) (* GEN END TAG OUTSIDE LET *)
                          
                  (* GEN BEGIN TAG OUTSIDE LET *) val Fpattern =  Fmt.HVbox [Fmt.Hbox (Fspine)] (* GEN END TAG OUTSIDE LET *)
                in
                  [Fmt.HVbox  [Fmt.Space, Fmt.String "|", Fmt.Space, Fpattern, Fmt.Space, Fmt.String "-->"],
                   Fmt.Spaces 2, Fmt.Vbox0 0 1 [formatPrg3 callname (Psi1', P2)],
                   Fmt.Break]
                  @ fmtCaseRest(L)
                end (* GEN END FUN BRANCH *)
          
              fun fmtCase ((Psi1, s1, P2)::L) =
                let
                  (* GEN BEGIN TAG OUTSIDE LET *) val Psi1' = psiName (Psi1, s1, Psi, 1) (* GEN END TAG OUTSIDE LET *)
                  (* GEN BEGIN TAG OUTSIDE LET *) val S = argsToSpine (s1, 1, T.Nil) (* GEN END TAG OUTSIDE LET *)
                  (* GEN BEGIN TAG OUTSIDE LET *) val Fspine = fmtSpine callname (Psi1, S) (* GEN END TAG OUTSIDE LET *)
          
                  (* GEN BEGIN TAG OUTSIDE LET *) val Fpattern =  Fmt.HVbox [Fmt.Hbox (Fspine)] (* GEN END TAG OUTSIDE LET *)
                in
                  Fmt.Vbox0 0 1 ([Fmt.HVbox  [Fmt.String "of", Fmt.Space, Fpattern, Fmt.Space, Fmt.String "-->"],
                                  Fmt.Spaces 2,
                                  Fmt.Vbox0 0 1 [formatPrg3 callname (Psi1', P2)], Fmt.Break]
                                 @ fmtCaseRest(L))
                end
          
          
          
              (* GEN BEGIN TAG OUTSIDE LET *) val F1 = Fmt.HVbox [formatPrg3 callname  (Psi, P1)] (* GEN END TAG OUTSIDE LET *)
              (* GEN BEGIN TAG OUTSIDE LET *) val Fbody = Fmt.HVbox [F1] (* GEN END TAG OUTSIDE LET *)
          
              (* GEN BEGIN TAG OUTSIDE LET *) val fmt = fmtCase(L) (* GEN END TAG OUTSIDE LET *)
            in
              Fmt.Vbox0 0 1 ([Fmt.String "case (", Fbody, Fmt.Space (* need space since there is one before Fbody *),
                             Fmt.String ")", Fmt.Break, fmt])
            end (* GEN END FUN BRANCH *)

          | (* GEN BEGIN FUN BRANCH *) formatLet callname (Psi, R as (T.Let (D, P1, T.Case (T.Cases L))), fmts) =
              Fmt.Vbox0 0 1 ([Fmt.String "let",
                              Fmt.Vbox0 0 1 (fmts @ [Fmt.Break]),
                              Fmt.Break,
                              Fmt.String "in", Fmt.Break,
                              Fmt.Spaces 2, formatLet callname (Psi, R, nil),
                              Fmt.Break,
                              Fmt.String "end"]) (* GEN END FUN BRANCH *)

          | (* GEN BEGIN FUN BRANCH *) formatLet callname (Psi, R as (T.Let (D as T.PDec (SOME name,F,_,_), P1, P2)), fmts) =
              Fmt.Vbox0 0 1 ([Fmt.String "let", Fmt.Break,
                              Fmt.Vbox0 0 1 ([Fmt.String name , Fmt.Space,
                                              Fmt.String"=",formatPrg3 callname (Psi, P1)]),
                              Fmt.Break,
                              Fmt.String "in", Fmt.Break,
                              Fmt.Spaces 2, formatPrg3 callname (I.Decl (Psi, D), P2),
                              Fmt.Break,
                              Fmt.String "end"]) (* GEN END FUN BRANCH *)

          | (* GEN BEGIN FUN BRANCH *) formatLet callname (Psi, R as (T.LetPairExp (D1 as I.Dec(SOME n1, _), D2 as T.PDec (SOME n2,F,_,_), P1, P2)), fmts) =
              Fmt.Vbox0 0 1 ([Fmt.String "let", Fmt.Break, Fmt.Spaces 2,
                              Fmt.Vbox0 0 1 ([Fmt.String "(", Fmt.String n1, Fmt.String ",", Fmt.Space, Fmt.String n2,  Fmt.String ")", Fmt.Space,
                                              Fmt.String "=", Fmt.Space, formatPrg3 callname (Psi, P1)]),
                              Fmt.Break,
                              Fmt.String "in", Fmt.Break,
                              Fmt.Spaces 2, formatPrg3 callname (I.Decl (I.Decl (Psi, T.UDec D1), D2), P2),
                              Fmt.Break,
                              Fmt.String "end"]) (* GEN END FUN BRANCH *)
          | (* GEN BEGIN FUN BRANCH *) formatLet callname (Psi, R as (T.LetUnit (P1, P2)), fmts) =
              Fmt.Vbox0 0 1 ([Fmt.String "let", Fmt.Break, Fmt.Spaces 2,
                              Fmt.Vbox0 0 1 ([Fmt.String "()", Fmt.Space,
                                              Fmt.String "=", Fmt.Space, formatPrg3 callname (Psi, P1)]),
                              Fmt.Break,
                              Fmt.String "in", Fmt.Break,
                              Fmt.Spaces 2, formatPrg3 callname (Psi, P2),
                              Fmt.Break,
                              Fmt.String "end"]) (* GEN END FUN BRANCH *)


        (* formatHead callname (index, Psi1, s, Psi2) = fmt'

           Invariant:
           If    Psi1 |- s : Psi2
           then  fmt is a format of the entire head
           where index represents the function name
           and   s the spine.
        *)
        and formatHead callname (name, (max, index), Psi', s, Psi) =
            let
        (*            val T.PDec (SOME name, _) = I.ctxLookup (Psi, index) *)
              (* GEN BEGIN TAG OUTSIDE LET *) val S = argsToSpine (s, I.ctxLength Psi - max, T.Nil) (* GEN END TAG OUTSIDE LET *)
        (*            val Fspine =   Print.formatSpine callname (T.coerceCtx Psi', S) *)
              (* GEN BEGIN TAG OUTSIDE LET *) val Fspine = fmtSpine callname (Psi', S) (* GEN END TAG OUTSIDE LET *)
            in
              Fmt.Hbox [Fmt.Space,
                        Fmt.HVbox (Fmt.String name :: Fmt.Break  :: Fspine)]
            end


        (* formatPrg2 ((max, index), Psi, L) = fmts'

           Invariant:
           If   |- Psi ctx
           and  Psi |- L a list of cases
           then fmts' list of pretty print formats of L
        *)
        fun (* GEN BEGIN FUN FIRST *) formatPrg2 (name, (max, index), Psi, nil, callname) = nil (* GEN END FUN FIRST *)
          | (* GEN BEGIN FUN BRANCH *) formatPrg2 (name, (max, index), Psi, (Psi', s, P) :: nil, callname) =
            let
              (* GEN BEGIN TAG OUTSIDE LET *) val Psi'' = psiName (Psi', s, Psi, 0) (* GEN END TAG OUTSIDE LET *)
              (* GEN BEGIN TAG OUTSIDE LET *) val fhead = if index = I.ctxLength Psi then "fun" else "and" (* GEN END TAG OUTSIDE LET *)
            in
              [Fmt.HVbox0 1 5 1
               [Fmt.String fhead, formatHead callname (name, (max, index), Psi'', s, Psi),
                Fmt.Space, Fmt.String "=",  Fmt.Break,
                formatPrg3 callname  (Psi'', P)], Fmt.Break]
            end (* GEN END FUN BRANCH *)
          | (* GEN BEGIN FUN BRANCH *) formatPrg2 (name, (max, index), Psi, (Psi', s, P) :: O, callname) =
            let
              (* GEN BEGIN TAG OUTSIDE LET *) val
                Psi'' = psiName (Psi', s, Psi, 0) (* GEN END TAG OUTSIDE LET *)
            in
              formatPrg2 (name, (max, index), Psi, O, callname) @
              [Fmt.HVbox0 1 5 1
               [Fmt.String "  |", formatHead callname (name, (max, index), Psi'', s, Psi),
                Fmt.Space, Fmt.String "=", Fmt.Break,
                formatPrg3 callname  (Psi'', P)], Fmt.Break]
            end (* GEN END FUN BRANCH *)




        fun (* GEN BEGIN FUN FIRST *) formatPrg11 (name, (max, index), Psi, T.Lam (D, P), callname) =
              formatPrg11 (name, (max, index+1), I.Decl (Psi, decName (T.coerceCtx Psi, D)), P, callname) (* GEN END FUN FIRST *)
          | (* GEN BEGIN FUN BRANCH *) formatPrg11 (name, (max, index), Psi, T.Case (T.Cases Os), callname) =
              formatPrg2 (name, (max, index), Psi, Os, callname) (* GEN END FUN BRANCH *)


        (* formatPrg1 ((max, index), Psi, P) = fmts'

           Invariant:
           If   |- Psi ctx
           and  Psi; . |- P :: F
           and  P is either a Lam .. | Case ... | Pair ...
           then fmts' is alist of pretty print formats of P
        *)
        fun (* GEN BEGIN FUN FIRST *) formatPrg1 (name::names, (max, index), Psi, T.PairPrg (P1, P2), callname) =
              formatPrg11 (name, (max, index), Psi, P1, callname)
              @ formatPrg1 (names, (max, index-1), Psi, P2, callname) (* GEN END FUN FIRST *)
          | (* GEN BEGIN FUN BRANCH *) formatPrg1 ([name], (max, index), Psi, P, callname) =
              formatPrg11 (name, (max, index), Psi, P, callname) (* GEN END FUN BRANCH *)

        (* formatPrg0 (Psi, P) = fmt'
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

        fun lookup (name :: names, proj :: projs) lemma =
            if lemma = proj then name else lookup (names, projs) lemma

        fun formatPrg0 ((names, projs), T.Rec (D as T.PDec (SOME _, F, _, _), P)) =
          let
        
            (* GEN BEGIN TAG OUTSIDE LET *) val max = 1 (* GEN END TAG OUTSIDE LET *) (* number of ih. *)
          in
            Fmt.Vbox0 0 1 (formatPrg1 (names, (max, max), I.Decl (I.Null, D), P, (* GEN BEGIN FUNCTION EXPRESSION *) fn lemma => lookup (names, projs) lemma (* GEN END FUNCTION EXPRESSION *)))
          end

    fun formatFun Args =
        (Names.varReset I.Null; formatPrg0 Args)

(*    fun formatLemmaDec (T.LemmaDec (names, P, F)) =
      Fmt.Vbox0 0 1 [formatFor (I.Null, F) names, Fmt.Break,
                     formatPrg (I.Null, P) names]
*)
    fun funToString Args = Fmt.makestring_fmt (formatFun Args)
    fun prgToString Args = Fmt.makestring_fmt (formatPrg3 ((* GEN BEGIN FUNCTION EXPRESSION *) fn _ => "?" (* GEN END FUNCTION EXPRESSION *))  Args)
(*   fun lemmaDecToString Args = Fmt.makestring_fmt (formatLemmaDec Args) *)

(*    fun prgToString Args names = "not yet implemented " *)

   fun (* GEN BEGIN FUN FIRST *) nameCtx I.Null = I.Null (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) nameCtx (I.Decl (Psi, T.UDec D)) =
          I.Decl (nameCtx Psi,
                  T.UDec (Names.decName (T.coerceCtx Psi, D))) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) nameCtx (I.Decl (Psi, T.PDec (NONE, F, TC1, TC2))) =
          let
            (* GEN BEGIN TAG OUTSIDE LET *) val Psi' = nameCtx Psi (* GEN END TAG OUTSIDE LET *)
            (* GEN BEGIN TAG OUTSIDE LET *) val I.NDec x = Names.decName (T.coerceCtx Psi', I.NDec NONE) (* GEN END TAG OUTSIDE LET *)
          in
            I.Decl (Psi', T.PDec (x, F, TC1, TC2))
          end (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) nameCtx (I.Decl (Psi, D as T.PDec (SOME n, F, _, _))) =
          I.Decl (nameCtx Psi, D) (* GEN END FUN BRANCH *)


   fun (* GEN BEGIN FUN FIRST *) flag NONE = "" (* GEN END FUN FIRST *)
     | (* GEN BEGIN FUN BRANCH *) flag (SOME _) = "*" (* GEN END FUN BRANCH *)

    (* formatCtx (Psi) = fmt'

       Invariant:
       If   |- Psi ctx       and Psi is already named
       then fmt' is a format describing the context Psi
    *)
    fun (* GEN BEGIN FUN FIRST *) formatCtx (I.Null) = [] (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) formatCtx (I.Decl (I.Null, T.UDec D)) =
        if !Global.chatter >= 4 then
          [Fmt.HVbox ([Fmt.Break, Print.formatDec (I.Null, D)])]
        else
          [Print.formatDec (I.Null, D)] (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) formatCtx (I.Decl (I.Null, T.PDec (SOME s, F, TC1, TC2))) =
        if !Global.chatter >= 4 then
          [Fmt.HVbox ([Fmt.Break, Fmt.String s, Fmt.Space,
                       Fmt.String ("::" ^ flag TC1), Fmt.Space, formatFor (I.Null, F)])]
        else
          [Fmt.String s, Fmt.Space, Fmt.String ("::" ^ flag TC1), Fmt.Space,
           formatFor (I.Null, F)] (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) formatCtx (I.Decl (Psi, T.UDec D)) =
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val G = T.coerceCtx Psi (* GEN END TAG OUTSIDE LET *)
        in
          if !Global.chatter >= 4 then
            formatCtx Psi @ [Fmt.String ",", Fmt.Break, Fmt.Break] @
            [Fmt.HVbox ([Fmt.Break, Print.formatDec (G, D)])]
          else
            formatCtx Psi @ [Fmt.String ",",  Fmt.Break] @
            [Fmt.Break, Print.formatDec (G, D)]
        end (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) formatCtx (I.Decl (Psi, T.PDec (SOME s, F, TC1, TC2))) =
        if !Global.chatter >= 4 then
          formatCtx Psi @ [Fmt.String ",", Fmt.Break, Fmt.Break] @
          [Fmt.HVbox ([Fmt.Break, Fmt.String s, Fmt.Space, Fmt.String ("::" ^ flag TC1), Fmt.Space, formatFor (Psi, F)])]
        else
          formatCtx Psi @ [Fmt.String ",",  Fmt.Break] @
          [Fmt.Break, Fmt.String s, Fmt.Space, Fmt.String ("::" ^ flag TC1), Fmt.Space,
           formatFor (Psi, F)] (* GEN END FUN BRANCH *)

    fun ctxToString Psi = Fmt.makestring_fmt (Fmt.HVbox (formatCtx Psi))

  in
    (* GEN BEGIN TAG OUTSIDE LET *) val formatFor = formatFor (* GEN END TAG OUTSIDE LET *)
    (* GEN BEGIN TAG OUTSIDE LET *) val forToString = forToString (* GEN END TAG OUTSIDE LET *)
    (* GEN BEGIN TAG OUTSIDE LET *) val formatFun = formatFun (* GEN END TAG OUTSIDE LET *)
    (* GEN BEGIN TAG OUTSIDE LET *) val formatPrg = formatPrg3 ((* GEN BEGIN FUNCTION EXPRESSION *) fn _ => "?" (* GEN END FUNCTION EXPRESSION *)) (* GEN END TAG OUTSIDE LET *)
(*    val formatLemmaDec = formatLemmaDec *)
    (* GEN BEGIN TAG OUTSIDE LET *) val evarName = evarName (* GEN END TAG OUTSIDE LET *)
    (* GEN BEGIN TAG OUTSIDE LET *) val evarReset = evarReset (* GEN END TAG OUTSIDE LET *)
    (* GEN BEGIN TAG OUTSIDE LET *) val nameEVar = nameEVar (* GEN END TAG OUTSIDE LET *)

    (* GEN BEGIN TAG OUTSIDE LET *) val prgToString = prgToString (* GEN END TAG OUTSIDE LET *)
    (* GEN BEGIN TAG OUTSIDE LET *) val funToString = funToString (* GEN END TAG OUTSIDE LET *)

    (* GEN BEGIN TAG OUTSIDE LET *) val nameCtx = nameCtx (* GEN END TAG OUTSIDE LET *)
    (* GEN BEGIN TAG OUTSIDE LET *) val formatCtx = (* GEN BEGIN FUNCTION EXPRESSION *) fn Psi => Fmt.HVbox (formatCtx Psi) (* GEN END FUNCTION EXPRESSION *) (* GEN END TAG OUTSIDE LET *)
    (* GEN BEGIN TAG OUTSIDE LET *) val ctxToString = ctxToString (* GEN END TAG OUTSIDE LET *)
(*    val lemmaDecToString = lemmaDecToString *)
  end
end (* GEN END FUNCTOR DECL *);  (* signature FUNPRINT *)

