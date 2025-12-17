Trans  DextSyn' DEXTSYN     struct module module module module module module module exception type Internallet  inlet  in(* Invariant   for each cid which has been internalize out of a block,
       internal(cid) = Const(n, i), where n is the number of some variables and
       i is the projection index
       for each type family
       internal(cid) = Type (cid'), where cid' is the orginial type family.
    *)
(* checkEOF f = r

      Invariant:
      If   f is the end of stream
      then r is a region

      Side effect: May raise Parsing.Error
    *)
let rec checkEOF(cons ((eOF,  , r),  , s')) r checkEOF(cons ((t,  , r),  , _)) error (r,  , "Expected `}', found " ^ toString t)(* Note that this message is inapplicable when we use
            checkEOF in stringToterm --rf *)
(* stringToDec s = dec

       Invariant:
       If   s is a string representing a declaration,
       then dec is the result of parsing it
       otherwise Parsing.error is raised.
    *)
let rec stringTodecs let let  inlet  inlet  inlet  in in declet rec stringToblockss let let  inlet  in in dl(* stringToWorlds s = W

       Invariant:
       If   s is a string representing an expression,
       then W is the result of parsing it
       otherwise Parsing.error is raised.
    *)
let rec stringToWorldss let let  inlet  inlet  in in t(* closure (G, V) = V'

       Invariant:
       {G}V = V'
    *)
let rec closure(null,  , v) v closure(decl (g,  , d),  , v) closure (g,  , pi ((d,  , maybe),  , v))(* internalizeBlock  (n, G, Vb, S) (L2, s) = ()

       Invariant:
       If   |- G ctx                the context of some variables
       and  G |- Vb :  type         the type of the block
       and  G |- L1, L2 decs
       and  G1, L1 |- L2 decs       block declarations still to be traversed
       and  G, b:Vb |- s : G1, L1
       and  n is the current projection
       then internalizeBlock adds new declarations into the signature that
              correspond to the block declarations.
    *)
let rec internalizeBlock_(nil,  , _) () internalizeBlock(n,  , g,  , vb,  , s)(dec (sOME name,  , v) :: l2,  , s) let let  inlet  in(* G, B |- V' : type *)
let  in(* G |- {B} V' : type *)
let  inlet  inlet  inlet  inlet  inlet  inlet  inlet  in in internalizeBlock (n + 1,  , g,  , vb,  , s) (l2,  , dot (exp (root (const cid,  , s)),  , s))(* makeSpine (n, G, S) = S'

       Invariant:
       If  G0 = G, G'
       and |G'| = n
       and G0 |- S : V >> V'   for some V, V'
       then S' extends S
       and G0 |- S' : V >> type.
    *)
let rec makeSpine(_,  , null,  , s) s makeSpine(n,  , decl (g,  , d),  , s) makeSpine (n + 1,  , g,  , app (root (bVar (n + 1),  , nil),  , s))(* interalizeCondec condec = ()

       Invariant:
       If   condec is a condec,
       then all pi declarations are internalized if condec was a blockdec
    *)
let rec internalizeCondec(cid,  , conDec _) () internalizeCondec(cid,  , conDef _) () internalizeCondec(cid,  , abbrevDef _) () internalizeCondec(cid,  , blockDec (name,  , _,  , gsome,  , lpi)) let let  inlet  inlet  inlet  inlet  inlet  inlet  inlet  in in internalizeBlock (1,  , gsome,  , vb,  , s') (lpi,  , shift) internalizeCondec(cid,  , skoDec _) ()(* sigToCtx () = ()

       Invariant:
       G is the internal representation of the global signature
       It converts every block declaration to a type family (stored in the global
       signature) and a list of declarations.
    *)
let rec internalizeSig() let let  in(* we might want to save max, here to restore the original
                 signature after parsing is over  --cs Thu Apr 17 09:46:29 2003 *)
let rec internalizeSig'n if n >= max then () else (internalizeCondec (n,  , sgnLookup n); internalizeSig' (n + 1)) in internalizeSig' 0(* Externalization *)
let rec dropSpine(0,  , s) s dropSpine(n,  , app (_,  , s)) dropSpine (n - 1,  , s)let rec makeSub(nil,  , s) s makeSub(app (u,  , s),  , s) makeSub (s,  , dot (exp u,  , s))let rec externalizeExp'(u as uni _) u externalizeExp'(pi ((d,  , dP),  , u)) pi ((externalizeDec d,  , dP),  , externalizeExp u) externalizeExp'(root (h as bVar _,  , s)) root (h,  , externalizeSpine s) externalizeExp'(root (h as const c,  , s)) (match constUni c with kind -> root (h,  , externalizeSpine s) type -> let let  inlet  in in root (proj (bidx b,  , i),  , externalizeSpine s')) externalizeExp'(root (proj _,  , _)) raise (domain) externalizeExp'(root (skonst _,  , _)) raise (domain) externalizeExp'(root (def _,  , _)) raise (domain) externalizeExp'(root (nSDef _,  , _)) raise (domain) externalizeExp'(root (fVar _,  , _)) raise (domain) externalizeExp'(root (fgnConst _,  , _)) raise (domain) externalizeExp'(redex (u,  , s)) redex (externalizeExp u,  , externalizeSpine s) externalizeExp'(lam (d,  , u)) lam (externalizeDec d,  , externalizeExp u) externalizeExp(u) externalizeExp' (normalize (u,  , id))(* Check : the translators hould only generate normal forms. Fix during the next pass --cs Thu Apr 17 17:06:24 2003 *)
 externalizeBlock(b as bidx _) b externalizeDec(dec (name,  , v)) dec (name,  , externalizeExp v) externalizeSpinenil nil externalizeSpine(app (u,  , s)) app (externalizeExp u,  , externalizeSpine s) externalizeSub(s as shift n) s externalizeSub(dot (f,  , s)) dot (externalizeFront f,  , externalizeSub s) externalizeFront(f as idx _) f externalizeFront(exp u) exp (externalizeExp u) externalizeFront(block b) block (externalizeBlock b) externalizeFront(f as undef) flet rec externalizePrg(n,  , lam (d,  , p)) lam (externalizeMDec (n,  , d),  , externalizePrg (n + 1,  , p)) externalizePrg(n,  , new p) new (externalizePrg (n,  , p)) externalizePrg(n,  , box (w,  , p)) box (w,  , externalizePrg (n,  , p)) externalizePrg(n,  , choose p) choose (externalizePrg (n,  , p)) externalizePrg(n,  , pairExp (u,  , p)) pairExp (externalizeExp u,  , externalizePrg (n,  , p)) externalizePrg(n,  , pairPrg (p1,  , p2)) pairPrg (externalizePrg (n,  , p1),  , externalizePrg (n,  , p2)) externalizePrg(n,  , pairBlock (b,  , p)) pairBlock (externalizeBlock b,  , externalizePrg (n,  , p)) externalizePrg(n,  , unit) unit externalizePrg(n,  , var k) var k externalizePrg(n,  , const c) const c externalizePrg(n,  , redex (p,  , s)) redex (externalizePrg (n,  , p),  , externalizeMSpine (n,  , s)) externalizePrg(n,  , rec (d,  , p)) rec (externalizeMDec (n,  , d),  , externalizePrg (n + 1,  , p)) externalizePrg(n,  , case (cases o)) case (cases (externalizeCases o)) externalizePrg(n,  , let (d,  , p1,  , p2)) let (externalizeMDec (n,  , d),  , externalizePrg (n,  , p1),  , externalizePrg (n + 1,  , p2))(* PClo should not be possible, since by invariant, parser
         always generates a program in normal form  --cs Thu Apr 17 16:56:07 2003
      *)
 externalizeMDec(n,  , uDec (d as dec (name,  , v as root (const a,  , s)))) (match sub (internal,  , a) with type (a') -> uDec (bDec (name,  , (a',  , makeSub (externalizeSpine s,  , shift n)))) _ -> uDec (externalizeDec d)) externalizeMDec(n,  , uDec d) uDec (externalizeDec d) externalizeMDec(n,  , pDec (s,  , f)) pDec (s,  , externalizeFor (n,  , f)) externalizeFor(n,  , world (w,  , f)) world (w,  , externalizeFor (n,  , f)) externalizeFor(n,  , all ((d,  , q),  , f)) all ((externalizeMDec (n,  , d),  , q),  , externalizeFor (n + 1,  , f)) externalizeFor(n,  , ex ((d,  , q),  , f)) ex ((externalizeDec d,  , q),  , externalizeFor (n + 1,  , f)) externalizeFor(n,  , true) true externalizeFor(n,  , and (f1,  , f2)) and (externalizeFor (n,  , f1),  , externalizeFor (n,  , f2)) externalizeMSpine(n,  , nil) nil externalizeMSpine(n,  , appExp (u,  , s)) appExp (externalizeExp u,  , externalizeMSpine (n,  , s)) externalizeMSpine(n,  , appBlock (b,  , s)) appBlock (externalizeBlock b,  , externalizeMSpine (n,  , s)) externalizeMSpine(n,  , appPrg (p,  , s)) appPrg (externalizePrg (n,  , p),  , externalizeMSpine (n,  , s)) externalizeCasesnil nil externalizeCases((psi,  , t,  , p) :: o) let let  in in (externalizeMCtx psi,  , externalizeMSub (n,  , t),  , externalizePrg (n,  , p)) :: externalizeCases o externalizeMSub(n,  , t as (shift _)) t externalizeMSub(n,  , dot (f,  , t)) dot (externalizeMFront (n,  , f),  , externalizeMSub (n,  , t)) externalizeMFront(n,  , f as (idx _)) f externalizeMFront(n,  , prg p) prg (externalizePrg (n,  , p)) externalizeMFront(n,  , exp u) exp (externalizeExp u) externalizeMFront(n,  , block b) block (externalizeBlock b) externalizeMFront(n,  , f as undef) f externalizeMCtxnull null externalizeMCtx(decl (psi,  , d)) decl (externalizeMCtx psi,  , externalizeMDec (ctxLength psi,  , d))(* Translation starts here *)
let rec transTerm(rtarrow (t1,  , t2)) let let  inlet  in in (s1 ^ " -> " ^ s2,  , c1 @ c2) transTerm(ltarrow (t1,  , t2)) let let  inlet  in in (s1 ^ " <- " ^ s2,  , c1 @ c2) transTerm(type) ("type",  , nil) transTerm(id s) let let  in in match constLookup qid with nONE -> (s,  , nil) sOME cid -> (match (sgnLookup cid) with blockDec _ -> (s ^ "'",  , nil) _ -> (s,  , nil)) transTerm(pi (d,  , t)) let let  inlet  in in ("{" ^ s1 ^ "}" ^ s2,  , c1 @ c2) transTerm(fn (d,  , t)) let let  inlet  in in ("[" ^ s1 ^ "]" ^ s2,  , c1 @ c2) transTerm(app (t1,  , t2)) let let  inlet  in in (s1 ^ " " ^ s2,  , c1 @ c2) transTerm(omit) ("_",  , nil) transTerm(paren (t)) let let  in in ("(" ^ s ^ ")",  , c) transTerm(of (t1,  , t2)) let let  inlet  in in (s1 ^ ":" ^ s2,  , c1 @ c2) transTerm(dot (t,  , s2)) let let  in in ("o_" ^ s2 ^ " " ^ s1,  , c1)(*      | transTerm (D.Dot (D.Id s1, s2)) =
        ("PROJ#" ^ s1 ^ "#" ^ s2, nil)
      | transTerm (D.Dot (D.Paren (D.Of (D.Id s1, t)), s2)) =
        ("PROJ#" ^ s1 ^ "#" ^ s2, [(s1, t)])
*)
 transDec(dec (s,  , t)) let let  in in (s ^ ":" ^ s',  , c)let rec transWorld(worldIdent s) let let  inlet  in in [cid] transWorld(plus (w1,  , w2)) transWorld w1 @ transWorld w2 transWorld(concat (w1,  , w2)) transWorld w1 @ transWorld w2 transWorld(times w) transWorld wlet rec transFor'(psi,  , d) let let  inlet  in in d'(* transFor (ExtDctx, ExtF) = (Psi, F)

       Invariant:
       If   |- ExtDPsi extdecctx
       and  |- ExtF extfor
       then |- Psi <= ExtDPsi
       and  Psi |- F <= ExtF
    *)
let rec transFor(psi,  , true) true transFor(psi,  , and (eF1,  , eF2)) and (transFor (psi,  , eF1),  , transFor (psi,  , eF2)) transFor(psi,  , forall (d,  , f)) let let  inlet  in in all ((uDec d',  , explicit),  , transFor (decl (psi,  , d'),  , f)) transFor(psi,  , exists (d,  , f)) let let  inlet  in in ex ((d',  , explicit),  , transFor (decl (psi,  , d'),  , f)) transFor(psi,  , forallOmitted (d,  , f)) let let  inlet  in in all ((uDec d',  , implicit),  , transFor (decl (psi,  , d'),  , f)) transFor(psi,  , existsOmitted (d,  , f)) let let  inlet  in in ex ((d',  , implicit),  , transFor (decl (psi,  , d'),  , f)) transFor(psi,  , world (w,  , eF)) world (worlds (transWorld w),  , transFor (psi,  , eF))(* stringToTerm s = U

       Invariant:
       If   s is a string representing an expression,
       then U is the result of parsing it
       otherwise Parsing.error is raised.
    *)
let rec stringToterms let let  inlet  inlet  in in t(* head (dH) = n

       Invariant:
       n is the name of the function head dH
    *)
let rec head(head s) s head(appLF (h,  , _)) head h head(appMeta (h,  , _)) head h(* lamClosure (F, P) = P'

       Invariant:
       If   . |- F formula
       and  . |- F = all D1. ... all Dn. F' formula
         for  . |- F' formula that does not commence with a universal quantifier
       and . |- P :: F'
       then P' = lam D1 ... lam Dn P
    *)
let rec lamClosure(all ((d,  , _),  , f),  , p) lam (d,  , lamClosure (f,  , p)) lamClosure(world (_,  , f),  , p) lamClosure (f,  , p) lamClosure(ex _,  , p) plet rec exists(c,  , []) raise (error "Current world is not subsumed") exists(c,  , c' :: cids) if c = c' then () else exists (c,  , cids)let rec subsumed([],  , cids') () subsumed(c :: cids,  , cids') (exists (c,  , cids'); subsumed (cids,  , cids'))let rec checkForWorld(world (w as worlds cids,  , f),  , t',  , worlds cids') let let  in(* check that W is at least as large as W' *)
 in (f,  , t',  , w) checkForWorldftW ftW(* dotn (t, n) = t'

       Invariant:
       If   Psi0 |- t : Psi
       and  |G| = n   for any G
       then Psi0, G[t] |- t : Psi, G
    *)
let rec dotn(t,  , 0) t dotn(t,  , n) dot1 (dotn (t,  , n - 1))(* append (Psi1, Psi2) = Psi3

       Invariant:
       If   |- Psi1 ctx
       and  |- Psi2 ctx
       then |- Psi3 = Psi1, Psi2 ctx
    *)
let rec append(psi,  , null) psi append(psi,  , decl (psi',  , d)) decl (append (psi,  , psi'),  , d)let rec parseTerm(psi,  , (s,  , v)) let let  inlet  inlet  in in ulet rec parseDec(psi,  , s) let let  inlet  inlet  inlet  in in d(* transDecs ((Psi, t), dDs, sc, W) = x

       Invariant:
       If   . |- t :: Psi
       and  Psi |- dDs decs
       and  W is the valid world
       and  sc is the success continuation that expects
            as input: (Psi', env')
                      where Psi' is the context after translating dDs
                      and   Psi' |- env' environment
                            are all variables introduced until this point
            as output: anything.
       then eventually x = ().     --cs
    *)
let rec transDecs(psi,  , empty,  , sc,  , w) sc (psi,  , w) transDecs(psi,  , formDecl (formD,  , ds),  , sc,  , w) (transForDec (psi,  , formD,  , ds,  , sc,  , w)) transDecs(psi,  , valDecl (valD,  , ds),  , sc,  , w) (transValDec (psi,  , valD,  , ds,  , sc,  , w)) transDecs(psi,  , newDecl (d,  , ds),  , sc,  , w) let let  in in (*          T.Let (T.PDec (NONE, T.True), T.Lam (D', transDecs (I.Decl (Psi, D'), Ds, sc, W)), T.Unit) *)
let (pDec (nONE,  , true),  , lam (d',  , transDecs (decl (psi,  , d'),  , ds,  , sc,  , w)),  , var 1)(* T.True is not right! -- cs Sat Jun 28 11:43:30 2003  *)
 transDecs_ raise (error "Constant declaration must be followed by a constant definition") lookup(null,  , n,  , s) raise (error ("Undeclared constant " ^ s)) lookup(decl (g,  , pDec (nONE,  , _)),  , n,  , s) lookup (g,  , n + 1,  , s) lookup(decl (g,  , uDec _),  , n,  , s) lookup (g,  , n + 1,  , s) lookup(decl (g,  , pDec (sOME s',  , f)),  , n,  , s) if s = s' then (n,  , forSub (f,  , shift n)) else lookup (g,  , n + 1,  , s)(* transHead (G, T, S) = (F', t')

       Invariant:
       If   G |- T : F
       and  G |- S : world{W}all{G'}F' >> F'
       then G |- t' : G'
    *)
 transHead(psi,  , head s,  , args) let let  in in transHead' ((f,  , id),  , nil,  , args) transHead(psi,  , appLF (h,  , t),  , args) transHead (psi,  , h,  , t :: args) transHead'((world (_,  , f),  , s),  , s,  , args) transHead' ((f,  , s),  , s,  , args) transHead'((all ((uDec (dec (_,  , v)),  , implicit),  , f'),  , s),  , s,  , args) let let  in in transHead' ((f',  , dot (exp x,  , s)),  , app (x,  , s),  , args) transHead'((all ((uDec (dec (_,  , v)),  , explicit),  , f'),  , s),  , s,  , t :: args) let let  inlet  inlet  in in transHead' ((f',  , dot (exp u,  , s)),  , app (u,  , s),  , args) transHead'((f,  , s),  , s,  , nil) ((f,  , s),  , s)(* spineToSub ((S, t), s) = s'

       Invariant:
       If  Psi' |- S spine
       and Psi'' |- t: Psi'
       and Psi'' |- s : Psi'''
       then  Psi'' |- s' : Psi''', Psi''''
    *)
 spineToSub((nil,  , _),  , s') s' spineToSub((app (u,  , s),  , t),  , s') dot (exp (eClo (u,  , t)),  , spineToSub ((s,  , t),  , s')) transPattern(p,  , (ex ((dec (_,  , v),  , implicit),  , f'),  , s)) transPattern (p,  , (f',  , dot (exp (eVar (ref nONE,  , null,  , eClo (v,  , coerceSub s),  , ref nil)),  , s))) transPattern(patInx (t,  , p),  , (ex ((dec (_,  , v),  , explicit),  , f'),  , s)) let let  inlet  inlet  in in pairExp (u,  , transPattern (p,  , (f',  , dot (exp u,  , s)))) transPattern(patUnit,  , (f,  , s)) unit(* other cases should be impossible by invariant
                                         F should be F.True
                                         --cs Sun Mar 23 10:38:57 2003 *)
(* transFun1 ((Psi, env), dDs, sc, W) = x

       Invariant:
       If   Psi |- dDs :: Psi'
       and  Psi |- env environment
       and  the top declaration is a function declaration
       and  W is the valid world
       and  sc is the success continuation that expects
            as input: (Psi', env')
                      where Psi' is the context after translating dDs
                      and   Psi' |- env' environment
                            are all variables introduced until this point
            as output: anything.
       then eventually x = ().     --cs
    *)
 transFun1(psi,  , (s',  , f),  , funDecl (fun (eH,  , eP),  , ds),  , sc,  , w) let let  inlet  in in transFun2 (psi,  , (s,  , f),  , funDecl (bar (eH,  , eP),  , ds),  , sc,  , fun cs -> case (cases cs),  , w) transFun1(psi,  , (s',  , f),  , funDecl (funAnd (eH,  , eP),  , ds),  , sc,  , w) raise (error "Mutual recursive functions not yet implemented") transFun1_ raise (error "Function declaration expected")(* transFun2 ((Psi, env), s, dDs, sc, k, W) = x

       Invariant:
       If   Psi |- dDs :: Psi'
       and  Psi |- env environment
       and  s is the name of the function currently being translated
       and  the top declaration is a function declaration
       and  the top declaration is a function declaration
       and  W is the valid world
       and  sc is the success continuation that expects
            as input: (Psi', env')
                      where Psi' is the context after translating dDs
                      and   Psi' |- env' environment
                            are all variables introduced until this point
            as output: anything.
       and  k is the continuation that expects
            as input: Cs a list of cases
            as ouput: A program P that corresponds to the case list Cs
       then eventually x = ().     --cs
    *)
 transFun2(psi,  , (s,  , f),  , funDecl (bar (eH,  , eP),  , ds),  , sc,  , k,  , w) transFun3 (psi,  , (s,  , f),  , eH,  , eP,  , ds,  , sc,  , k,  , w) transFun2(psi,  , (s,  , f),  , ds,  , sc,  , k,  , w) let let  inlet  in in (p',  , ds)(* transFun3 ((Psi, env), s, eH, eP, Ds, sc, k, W) = x

       Invariant:
       If   Psi |- dDs :: Psi'
       and  Psi |- env environment
       and  s is the name of the function currently being translated
       and  eH is the head of the function
       and  eP its body
       and  W is the valid world
       and  Ds are the remaining declarations
       and  sc is the success continuation that expects
            as input: (Psi', env')
                      where Psi' is the context after translating dDs
                      and   Psi' |- env' environment
                            are all variables introduced until this point
            as output: anything.
       and  k is the continuation that expects
            as input: Cs a list of cases
            as ouput: A program P that corresponds to the case list Cs
       then eventually x = ().     --cs
    *)
 transFun3(psi,  , (s,  , f),  , eH,  , eP,  , ds,  , sc,  , k,  , w) let let  inlet  inlet  inlet  in(*                val F' = T.forSub (F, t) *)
let  inlet  inlet  inlet  in(* |Psi''| = m0 + m' *)
let  in(* Psi0, Psi'[^m0] |- t0 : Psi' *)
(*        val t1 = T.Dot (T.Prg (T.Root (T.Var (m'+1), T.Nil)), T.Shift (m'))   (* BUG !!!! Wed Jun 25 11:23:13 2003 *)
                                        (* Psi0, Psi'[^m0] |- t1 : F[^m0]  *)
*)
let  in(*        val _ = print (TomegaPrint.forToString (Names.ctxName (T.coerceCtx Psi''), myF) ^ "\n") *)
let  in in transFun2 (psi,  , (s,  , f),  , ds,  , sc,  , fun cs -> k ((psi'',  , t'',  , p) :: cs),  , w)(* transForDec ((Psi, env), eDf, dDs, sc, W) = x

       Invariant:
       If   Psi |- dDs :: Psi'
       and  Psi |- env environment
       and  Psi |- eDf is a theorem declaration.
       and  W is the valid world
       and  dDs are the remaining declarations
       and  sc is the success continuation that expects
            as input: (Psi', env')
                      where Psi' is the context after translating dDs
                      and   Psi' |- env' environment
                            are all variables introduced until this point
            as output: anything.
       then eventually x = ().     --cs
    *)
 transForDec(psi,  , form (s,  , eF),  , ds,  , sc,  , w) let let  inlet  inlet  in(*        val _ = print s
          val _ = print " :: "
          val _ = print (TomegaPrint.forToString (T.embedCtx G, F'') ^ "\n") *)
let  inlet  inlet  in in let (d,  , box (w,  , p),  , transDecs (decl (psi,  , d),  , ds',  , (fun p' -> sc p'),  , w))(* transValDec ((Psi, env), dDv, dDs, sc, W) = x

       Invariant:
       If   Psi |- dDs :: Psi'
       and  Psi |- env environment
       and  Psi |- dDv value declaration
       and  W is the valid world
       and  dDs are the remaining declarations
       and  sc is the success continuation that expects
            as input: (Psi', env')
                      where Psi' is the context after translating dDs
                      and   Psi' |- env' environment
                            are all variables introduced until this point
            as output: anything.
       then eventually x = ().     --cs
    *)
 transValDec(psi,  , val (ePat,  , eP,  , eFopt),  , ds,  , sc,  , w) let let  inlet  inlet  inlet  inlet  inlet  in(*        val t = T.Dot (T.Prg Pat', T.id)  was --cs Tue Jun 24 13:04:55 2003 *)
let  inlet  inlet  in in let (d,  , p,  , case (cases [(psi'',  , t,  , p'')]))(* transProgS ((Psi, env), ExtP, F, W) = P
       transProgI ((Psi, env), ExtP, W) = (P, F)
       Invariant:
       If   ExtP contains free variables among (Psi, env)
       and  ExtP is a program defined in (Psi, env)
       and  W is a world
       and  Exists Psi |- F : formula
       then Psi |- P :: F
    *)
 transProgI(psi,  , eP,  , ft,  , w) transProgIN (psi,  , eP,  , forSub ft,  , w) transProgIN(psi,  , unit,  , true,  , w) unit transProgIN(psi,  , p as inx (s,  , eP),  , ex ((dec (_,  , v),  , explicit),  , f'),  , w) let let  inlet  in in pairExp (u,  , p') transProgIN(psi,  , let (eDs,  , eP),  , f,  , w) transDecs (psi,  , eDs,  , fun (psi',  , w') -> transProgI (psi',  , eP,  , (f,  , shift (ctxLength psi' - ctxLength psi)),  , w'),  , w) transProgIN(psi,  , choose (eD,  , eP),  , f,  , w) let let  inlet  in in choose (lam (uDec d',  , transProgI (psi'',  , eP,  , (f,  , shift 1),  , w))) transProgIN(psi,  , new (nil,  , eP),  , f,  , w) transProgIN (psi,  , eP,  , f,  , w) transProgIN(psi,  , new (eD :: eDs,  , eP),  , f,  , w) let let  inlet  in in new (lam (uDec d',  , transProgI (psi'',  , new (eD :: eDs,  , eP),  , (f,  , shift 1),  , w))) transProgIN(psi,  , p as appTerm (eP,  , s),  , f,  , w) let let  inlet  in(* check that F == F' *)
 in p'(*      | transProgIN ((Psi, env), D.Pair (EP1, EP2), T.And (F1, F2), W) =
        let
          val P1 = transProgIN ((Psi, env), EP1, F1, W)
          val P2 = transProgIN ((Psi, env), EP2, F2, W)
        in
          T.PairPrg (P1, P2)
        end
      | transProgIN ((Psi, env), P as D.AppProg (EP1, EP2), F, W) =
        let
          val (P', (F', _)) = transProgS ((Psi, env), P, W)
          val ()  = ()   (* check that F == F' *)
        in
          P'
        end
      | transProgIN ((Psi, env), P as D.AppTerm (EP, s), F, W) =
        let
          val (P', (F', _)) = transProgS ((Psi, env), P, W)
          val ()  = ()   (* check that F == F' *)
        in
          P'
        end
      | transProgIN ((Psi, env), P as D.Inx (s, EP), T.Ex (I.Dec (_, V), F'), W) =
        let
          val (U, V) = parseTerm ((Psi, env), s)
          val P' = transProgI ((Psi, env), EP, (F', T.Dot (T.Exp U, T.id)), W)
        in
          T.PairExp (U, P')
        end
      | transProgIN ((Psi, env), D.Const name, F, W) =
        let
          val lemma = T.lemmaName name
          val F' = T.lemmaFor lemma
          val () = ()    (* check that F == F' *)
        in
          T.Root (T.Const lemma, T.Nil)
        end

(*      | transProgIN (Psi, D.Lam (s, EP)) =
        let
          val dec = stringTodec s
          val (I.Decl (Psi, (D, _, _)), P, F') = transProgI (I.Decl (ePsi, dec), EP)
        in
          (Psi, T.Lam (T.UDec D, P), T.All (D, F'))
        end
*)


      | transProgIN ((Psi, env), D.New (s, EP), F, W) =
          let
            val G = Names.ctxName (T.coerceCtx Psi)
            val _ = print (Print.ctxToString (I.Null, G) ^ "\n")
            val (U, V) = parseTerm ((Psi, env), s ^ " type")
            val _ = print (Print.expToString (G, U) ^ "\n")

          fun extract (G, Us) = extractW (G, Whnf.whnf Us)
          and extractW (G, (I.Pi ((D as I.Dec (_, _), _), V'), s)) =
                extract (I.Decl(G, I.decSub (D, s)), (V', I.dot1 s))
            | extractW (G, _) = G

          val G' = extract (I.Null, (U, I.id))
          val Dlist = T.ctxToBDecs (T.coerceCtx Psi, G', W)

          fun project ((G, env), []) = (env, 1)   (* is this the right starting point --cs *)
            | project ((G, env), x :: N) =
              let
                val (env', k) = project ((G, env), N)
                val U = I.Root (I.Proj (I.Bidx 1, k), I.Nil)
                val V =  TypeCheck.infer' (G, U)
              in
                ((U, V, x) :: env', k+1)
              end

          fun extend ((Psi', env'), []) = (Psi', env')
            | extend ((Psi', env'), (N, D) :: Dlist') =
              let
                val (Psi'', env'') = extend ((Psi', env'),  Dlist')
                val Psi''' = I.Decl (Psi'', T.UDec D)
                val I.BDec (_, (cid, s)) = D
                val G''' = T.coerceCtx Psi'''
                val env''' = map (fn (U, V, name) => (I.EClo (U, I.shift), I.EClo (V, I.shift), name)) env''
                val (env'''', _) = project ((G''', env'''), N)
              in
                (Psi''',  env'''')
               end

           val (Psi', env') = extend ((Psi, env), Dlist)
           val _ = printCtx (Names.ctxName (T.coerceCtx Psi'), env')

          fun universalClosure ([], F) = F
            | universalClosure ((_, D) :: Ds, F)  = T.All (T.UDec D, universalClosure (Ds, F))

          val (P', (F, t)) = transProgS ((Psi, env), EP, W)

          in
            T.Unit
          end

*)
 transProgS(psi,  , unit,  , w,  , args) (unit,  , (true,  , id)) transProgS(psi,  , appTerm (eP,  , s),  , w,  , args) transProgS (psi,  , eP,  , w,  , s :: args) transProgS(psi,  , const name,  , w,  , args) let (*         val lemma = T.lemmaName name
           val F = T.lemmaFor lemma *)
let  inlet  in in (redex (var n,  , s),  , fs') transProgS(psi,  , choose (eD,  , eP),  , w,  , args) let let  inlet  in in (choose (lam (uDec d',  , p)),  , (f,  , t)) transProgS(psi,  , new (nil,  , eP),  , w,  , args) transProgS (psi,  , eP,  , w,  , args) transProgS(psi,  , new (eD :: eDs,  , eP),  , w,  , args) let let  inlet  inlet  inlet  inlet  in in (new (lam (uDec d',  , p)),  , (f',  , id))(* bug: forgot to raise F[t] to F' --cs Tue Jul  1 10:49:52 2003 *)
 transProgS'(psi,  , (world (_,  , f),  , s),  , w,  , args) transProgS' (psi,  , (f,  , s),  , w,  , args) transProgS'(psi,  , (all ((uDec (dec (_,  , v)),  , implicit),  , f'),  , s),  , w,  , args) let let  inlet  in(*        val X = I.EVar (ref NONE, I.Null, I.EClo (V, T.coerceSub s), ref nil) *)
let  in in (appExp (normalize (x,  , id),  , s),  , fs') transProgS'(psi,  , (all ((uDec (dec (_,  , v)),  , explicit),  , f'),  , s),  , w,  , t :: args) let let  inlet  in(*        val (F'', s'', _) = checkForWorld (F', T.Dot (T.Exp U, s), W) *)
 in (appExp (u,  , s),  , fs') transProgS'(psi,  , (f,  , s),  , _,  , nil) (nil,  , (f,  , s))(*
     | transProgS ((Psi, env), D.Pair (EP1, EP2), W) =
        let
          val (P1, (F1, t1)) = transProgS ((Psi, env), EP1, W)
          val (P2, (F2, t2)) = transProgS ((Psi, env), EP2, W)
        in
          (T.PairPrg (P1, P2), (T.And (F1, F2), T.comp (t1, t2)))
        end

     | transProgS ((Psi, env), D.AppProg (EP1, EP2), W) =
        let
          val (P1, (T.And (F1, F2), t)) = transProgS ((Psi, env), EP1, W)
          val P2 = transProgIN ((Psi, env), EP2, T.FClo (F1, t), W)
          val (F'', t'', W) = checkForWorld (F2, t, W)
        in
          (T.Redex (P1, T.AppPrg (P2, T.Nil)), (F'', t''))
        end


      | transProgS ((Psi, env), P as D.Inx (s, EP), W) =  raise Error "Cannot infer existential types"

(*      | transProgS ((Psi, env), D.Lam (s, EP), W) =
        let
          val dec = stringTodec s
          val (I.Decl (Psi', (D, _, _)), P, F) = transProgI (I.Decl (Psi, dec), EP)
          val (F', t', _) = checkForWorld (F, T.id, W)
        in
          (T.Lam (T.UDec D, P), (T.All (D, F'), t'))
        end
*)
      | transProgS ((Psi, env), D.New (s, eP), W)  =
        let
          val _ = print "["
          val G = Names.ctxName (T.coerceCtx Psi)
          val _ = print (Print.ctxToString (I.Null, G) ^ "\n")
          val (U, V) = parseTerm ((Psi, env), s ^ " type")
(*        val _ = print (Print.expToString (G, U) ^ "\n") *)

          fun extract (G, Us) = extractW (G, Whnf.whnf Us)
          and extractW (G, (I.Pi ((D as I.Dec (_, _), _), V'), s)) =
                extract (I.Decl(G, I.decSub (D, s)), (V', I.dot1 s))
            | extractW (G, _) = G

          val G' = extract (I.Null, (U, I.id))
          val Dlist = T.ctxToBDecs (T.coerceCtx Psi, G', W)

          fun project ((G, env), []) = (env, 1)   (* is this the right starting point --cs *)
            | project ((G, env), x :: N) =
              let
                val (env', k) = project ((G, env), N)
                val U = I.Root (I.Proj (I.Bidx 1, k), I.Nil)
                val V =  TypeCheck.infer' (G, U)
              in
                ((U, V, x) :: env', k+1)
              end

          fun extend ((Psi', env'), []) = (Psi', env')
            | extend ((Psi', env'), (N, D) :: Dlist') =
              let
                val (Psi'', env'') = extend ((Psi', env'),  Dlist')
                val Psi''' = I.Decl (Psi'', T.UDec D)
                val I.BDec (_, (cid, s)) = D
                val G''' = T.coerceCtx Psi'''
                val env''' = map (fn (U, V, name) =>
                    (I.EClo (U, I.shift), I.EClo (V, I.shift), name)) env''
                val (env'''', _) = project ((G''', env'''), N)
              in
                (Psi''',  env'''')
               end

          val (Psi', env') = extend ((Psi, env), Dlist)
          val _ = printCtx (Names.ctxName (T.coerceCtx Psi'), env')

          fun universalClosure ([], F) = F
            | universalClosure ((_, D) :: Ds, F)  = T.All (T.UDec D, universalClosure (Ds, F))

          val (P', (F, t)) = transProgS ((Psi, env), eP, W)
          val F' = T.forSub (F, t)
          val F'' = universalClosure (Dlist, F')
          val P'' = lamClosure (F'', P')
        in
          (P'', (F'', T.id))
        end
*)
(* transProgram Ds = P

       Invariant:
       If Ds is a list of declarations then P is
       the translated program, that does not do anything
    *)
let rec transProgramds transDecs (null,  , ds,  , fun (psi,  , w) -> (unit),  , worlds [])let  in(*    val makePattern = makePattern *)
(*    val transPro = fn P => let val (P', _) = transProgS ((I.Null, []), P, T.Worlds []) in P' end *)
let  inlet  inlet  in(*    val transDecs = fn Ds => transDecs ((I.Null, []), NONE, Ds, fn (Psi,  W) => T.Unit, T.Worlds [])
*)
end