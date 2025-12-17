FunPrint  Formatter FORMATTER    Names NAMES    Print PRINT    Print Formatter  Formatter    FUNPRINT  struct (*! structure FunSyn = FunSyn' !*)
module module module module module (* Invariant:

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
(* formatCtxBlock (G, (G1, s1)) = (G', s', fmts')

       Invariant:
       If   |- G ctx
       and  G |- G1 ctx
       and  G2 |- s1 : G
       then G' = G2, G1 [s1]
       and  G' |- s' : G, G1
       and  fmts is a format list of G1[s1]
    *)
let rec formatCtxBlock(g,  , (null,  , s)) (g,  , s,  , nil) formatCtxBlock(g,  , (decl (null,  , d),  , s)) let let  inlet  in in (decl (g,  , d'),  , dot1 s,  , [fmt]) formatCtxBlock(g,  , (decl (g',  , d),  , s)) let let  inlet  inlet  in in (decl (g'',  , d''),  , dot1 s'',  , fmts @ [string ","; break; fmt])(* formatFor' (G, (F, s)) = fmts'

       Invariant:
       If   |- G ctx
       and  G |- s : Psi'
       and  Psi' |- F formula
       then fmts' is a list of formats for F
    *)
let rec formatFor'(g,  , (all (lD,  , f),  , s)) (match lD with prim d -> let let  in in [string "{{"; formatDec (g,  , decSub (d',  , s)); string "}}"; break] @ formatFor' (decl (g,  , d'),  , (f,  , dot1 s)) block (ctxBlock (l,  , g')) -> let let  in in [string "{"; hbox fmts; string "}"; break] @ formatFor' (g'',  , (f,  , s''))) formatFor'(g,  , (ex (d,  , f),  , s)) let let  in in [string "[["; formatDec (g,  , decSub (d',  , s)); string "]]"; break] @ formatFor' (decl (g,  , d'),  , (f,  , dot1 s)) formatFor'(g,  , (true,  , s)) [string "True"](* formatFor (Psi, F) names = fmt'
       formatForBare (Psi, F) = fmt'

       Invariant:
       If   |- Psi ctx
       and  Psi |- F = F1 ^ .. ^ Fn formula
       and  names is a list of n names,
       then fmt' is the pretty printed format
    *)
let rec formatFor(psi,  , f)names let let rec nameLookupindex nth (names,  , index)(* formatFor1 (index, G, (F, s)) = fmts'

           Invariant:
           If   |- G ctx
           and  G |- s : Psi
           and  Psi |- F1 ^ .. ^ F(index-1) ^ F formula
           then fmts' is a list of pretty printed formats for F
        *)
let rec formatFor1(index,  , g,  , (and (f1,  , f2),  , s)) formatFor1 (index,  , g,  , (f1,  , s)) @ [break] @ formatFor1 (index + 1,  , g,  , (f2,  , s)) formatFor1(index,  , g,  , (f,  , s)) [string (nameLookup index); space; string "::"; space; hVbox (formatFor' (g,  , (f,  , s)))]let rec formatFor0args vbox0 0 1 (formatFor1 args) in (varReset null; formatFor0 (0,  , makectx psi,  , (f,  , id)))let rec formatForBare(g,  , f) hVbox (formatFor' (g,  , (f,  , id)))(* formatPro (Psi, P) names = fmt'

       Invariant:
       If   |- Psi ctx
       and  Psi; . |- P = rec x. (P1, P2, .. Pn) in F
       and  names is a list of n names,
       then fmt' is the pretty printed format of P
    *)
let rec formatProargsnames let let rec nameLookupindex nth (names,  , index)(* blockName (G1, G2) = G2'

           Invariant:
           If   G1 |- G2 ctx
           then G2' = G2 modulo new non-conficting variable names.
        *)
let rec blockName(g1,  , g2) let let rec blockName'(g1,  , null) (g1,  , null) blockName'(g1,  , decl (g2,  , d)) let let  inlet  in in (decl (g1',  , d'),  , decl (g2',  , d'))let  in in g2'(* ctxBlockName (G1, CB) = CB'

           Invariant:
           If   G1 |- CB ctxblock
           then CB' = CB modulo new non-conficting variable names.
        *)
let rec ctxBlockName(g1,  , ctxBlock (name,  , g2)) ctxBlock (name,  , blockName (g1,  , g2))(* decName (G, LD) = LD'

           Invariant:
           If   G1 |- LD lfdec
           then LD' = LD modulo new non-conficting variable names.
        *)
let rec decName(g,  , prim d) prim (decName (g,  , d)) decName(g,  , block cB) block (ctxBlockName (g,  , cB))(* numberOfSplits Ds = n'

           Invariant:
           If   Psi, Delta |- Ds :: Psi', Delta'
           then n'= |Psi'| - |Psi|
        *)
let rec numberOfSplitsds let let rec numberOfSplits'(empty,  , n) n numberOfSplits'(new (_,  , ds),  , n) numberOfSplits' (ds,  , n) numberOfSplits'(app (_,  , ds),  , n) numberOfSplits' (ds,  , n) numberOfSplits'(lemma (_,  , ds),  , n) numberOfSplits' (ds,  , n) numberOfSplits'(split (_,  , ds),  , n) numberOfSplits' (ds,  , n + 1) numberOfSplits'(left (_,  , ds),  , n) numberOfSplits' (ds,  , n) numberOfSplits'(right (_,  , ds),  , n) numberOfSplits' (ds,  , n) in numberOfSplits' (ds,  , 0)(* psiName (Psi1, s, Psi2, l) = Psi1'

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
let rec psiName(psi1,  , s,  , psi2,  , l) let let rec nameDec(d as dec (sOME _,  , _),  , name) d nameDec(dec (nONE,  , v),  , name) dec (sOME name,  , v)let rec namePsi(decl (psi,  , prim d),  , 1,  , name) decl (psi,  , prim (nameDec (d,  , name))) namePsi(decl (psi,  , lD as prim d),  , n,  , name) decl (namePsi (psi,  , n - 1,  , name),  , lD) namePsi(decl (psi,  , block (ctxBlock (label,  , g))),  , n,  , name) let let  in in decl (psi',  , block (ctxBlock (label,  , g'))) nameG(psi,  , null,  , n,  , name,  , k) (k n,  , null) nameG(psi,  , decl (g,  , d),  , 1,  , name,  , k) (psi,  , decl (g,  , nameDec (d,  , name))) nameG(psi,  , decl (g,  , d),  , n,  , name,  , k) let let  in in (psi',  , decl (g',  , d))let rec ignore(s,  , 0) s ignore(dot (_,  , s),  , k) ignore (s,  , k - 1) ignore(shift n,  , k) ignore (dot (idx (n + 1),  , shift (n + 1)),  , k - 1)let rec copyNames(shift n,  , g as decl _)psi1 copyNames (dot (idx (n + 1),  , shift (n + 1)),  , g) psi1 copyNames(dot (exp _,  , s),  , decl (g,  , _))psi1 copyNames (s,  , g) psi1 copyNames(dot (idx k,  , s),  , decl (g,  , dec (nONE,  , _)))psi1 copyNames (s,  , g) psi1 copyNames(dot (idx k,  , s),  , decl (g,  , dec (sOME name,  , _)))psi1 let let  in in copyNames (s,  , g) psi1' copyNames(shift _,  , null)psi1 psi1let rec psiName'(null) null psiName'(decl (psi,  , d)) let let  in in decl (psi',  , decName (makectx psi',  , d)) in psiName' (copyNames (ignore (s,  , l),  , makectx psi2) psi1)(* merge (G1, G2) = G'

           Invariant:
           G' = G1, G2
        *)
let rec merge(g1,  , null) g1 merge(g1,  , decl (g2,  , d)) decl (merge (g1,  , g2),  , d)(* formatCtx (Psi, G) = fmt'

           Invariant:
           If   |- Psi ctx
           and  Psi |- G ctx
           then fmt' is a pretty print format of G
        *)
let rec formatCtx(psi,  , g) let let  inlet rec formatCtx'(null) nil formatCtx'(decl (null,  , dec (sOME name,  , v))) [string name; string ":"; formatExp (g0,  , v)] formatCtx'(decl (g,  , dec (sOME name,  , v))) (formatCtx' g) @ [string ","; break; string name; string ":"; formatExp (merge (g0,  , g),  , v)] in hbox (string "|" :: (formatCtx' g @ [string "|"]))(* formatTuple (Psi, P) = fmt'

           Invariant:
           If   |- Psi ctx
           and  Psi; Delta |- P = Inx (M1, Inx ... (Mn, Unit))
           then fmt' is a pretty print format of (M1, .., Mn)
        *)
let rec formatTuple(psi,  , p) let let rec formatTuple'(unit) nil formatTuple'(inx (m,  , unit)) [formatExp (makectx psi,  , m)] formatTuple'(inx (m,  , p')) (formatExp (makectx psi,  , m) :: string "," :: break :: formatTuple' p') in match p with (inx (_,  , unit)) -> hbox (formatTuple' p) _ -> hVbox0 1 1 1 (string "(" :: (formatTuple' p @ [string ")"]))(* formatSplitArgs (Psi, L) = fmt'

           Invariant:
           If   |- Psi ctx
           and  L = (M1, .., Mn)
           and  Psi |- Mk:Ak for all 1<=k<=n
           then fmt' is a pretty print format of (M1, .., Mn)
        *)
let rec formatSplitArgs(psi,  , l) let let rec formatSplitArgs'(nil) nil formatSplitArgs'(m :: nil) [formatExp (makectx psi,  , m)] formatSplitArgs'(m :: l) (formatExp (makectx psi,  , m) :: string "," :: break :: formatSplitArgs' l) in if length l = 1 then hbox (formatSplitArgs' l) else hVbox0 1 1 1 (string "(" :: (formatSplitArgs' l @ [string ")"]))(* frontToExp (Ft) = U'

           Invariant:
           G |- Ft = U' : V   for a G, V
        *)
let rec frontToExp(idx k) root (bVar k,  , nil) frontToExp(exp (u)) u(* formatDecs1 (Psi, Ds, s, L) = L'

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
let rec formatDecs1(psi,  , split (xx,  , ds),  , dot (ft,  , s1),  , l) formatDecs1 (psi,  , ds,  , s1,  , frontToExp (ft) :: l) formatDecs1(psi,  , empty,  , s1,  , l) l formatDecs1(psi,  , ds,  , shift n,  , l) formatDecs1 (psi,  , ds,  , dot (idx (n + 1),  , shift (n + 1)),  , l)(* formatDecs0 (Psi, Ds) = (Ds', S')

           Invariant:
           If   |- Psi ctx
           and  Psi ; Delta |- Ds : Psi', Delta'
           and  Ds = App M1 ... App Mn Ds'   (where Ds' starts with Split)
           then S' = (M1, M2 .. Mn)
           and  Psi1, Delta1 |- Ds' : Psi1', Delta1'
                (for some Psi1, Delta1, Psi1', Delta1')
        *)
let rec formatDecs0(psi,  , app ((xx,  , m),  , ds)) let let  in in (ds',  , app (m,  , s)) formatDecs0(psi,  , ds) (ds,  , nil)(* formatDecs (index, Psi, Ds, (Psi1, s1)) = fmt'

           Invariant:
           If   |- Psi ctx
           and  Psi; Delta |- Ds : Psi'; Delta'
           and  Psi1 |- s1 : Psi, Psi'
           then fmt' is a pretty print format of Ds
        *)
let rec formatDecs(index,  , psi,  , ds as app ((xx,  , _),  , p),  , (psi1,  , s1)) let let  inlet  inlet  in in hbox [formatSplitArgs (psi1,  , l'); space; string "="; break; hVbox (string name :: break :: formatSpine (makectx psi,  , s))] formatDecs(index,  , psi,  , new (b as ctxBlock (_,  , g),  , ds),  , (psi1,  , s1)) let let  inlet  in in vbox [formatCtx (psi,  , g); break; fmt] formatDecs(index,  , psi,  , lemma (lemma,  , ds),  , (psi1,  , s1)) let let  inlet  inlet  in in hbox [formatSplitArgs (psi1,  , l'); space; string "="; break; hVbox (string (nth (names,  , index)) :: break :: formatSpine (makectx psi,  , s))] formatDecs(index,  , psi,  , left (_,  , ds),  , (psi1,  , s1)) let let  in in fmt formatDecs(index,  , psi,  , right (_,  , ds),  , (psi1,  , s1)) let let  in in fmt(* formatLet (Psi, P, fmts) = fmts'

           Invariant:
           If   |- Psi ctx
           and  Psi; Delta |- P = Let . Case P' :: F
           and  fmts is a list of pretty print formats of P
           then fmts' extends fmts
           and  fmts also includes a pretty print format for P'
        *)
let rec formatLet(psi,  , let (ds,  , case (opts ((psi1,  , s1,  , p1 as let _) :: nil))),  , fmts) let let  inlet  in in formatLet (psi1',  , p1,  , fmts @ [fmt; break]) formatLet(psi,  , let (ds,  , case (opts ((psi1,  , s1,  , p1) :: nil))),  , fmts) let let  inlet  in in vbox0 0 1 ([string "let"; break; spaces 2; vbox0 0 1 (fmts @ [fmt]); break; string "in"; break; spaces 2; formatPro3 (psi1',  , p1); break; string "end"])(* formatPro3 (Psi, P) = fmt

           Invariant:
           If   |- Psi ctx
           and  Psi; Delta |- P :: F
           and  P = let .. in .. end | <..,..> | <>
           then fmt is a pretty print of P
        *)
 formatPro3(psi,  , p as unit) formatTuple (psi,  , p) formatPro3(psi,  , p as inx _) formatTuple (psi,  , p) formatPro3(psi,  , p as let _) formatLet (psi,  , p,  , nil)(* argsToSpine (Psi1, s, S) = S'

           Invariant:
           If   Psi1 |- s = M1 . M2 .. Mn. ^|Psi1|: Psi2
           and  Psi1 |- S : V1 > {Psi2} V2
           then Psi1 |- S' : V1 > V2
           and S' = S, M1 .. Mn
           where
           then Fmts is a list of arguments
        *)
let rec argsToSpine(s,  , null,  , s) s argsToSpine(shift (n),  , psi,  , s) argsToSpine (dot (idx (n + 1),  , shift (n + 1)),  , psi,  , s) argsToSpine(dot (ft,  , s),  , decl (psi,  , d),  , s) argsToSpine (s,  , psi,  , app (frontToExp ft,  , s))(* formatHead (index, Psi1, s, Psi2) = fmt'

           Invariant:
           If    Psi1 |- s : Psi2
           then  fmt is a format of the entire head
           where index represents the function name
           and   s the spine.
        *)
let rec formatHead(index,  , psi',  , s,  , psi) hbox [space; hVbox (string (nameLookup index) :: break :: formatSpine (makectx psi',  , argsToSpine (s,  , psi,  , nil)))](* formatPro2 (index, Psi, L) = fmts'

           Invariant:
           If   |- Psi ctx
           and  Psi |- L a list of cases
           then fmts' list of pretty print formats of L
        *)
let rec formatPro2(index,  , psi,  , nil) nil formatPro2(index,  , psi,  , (psi',  , s,  , p) :: nil) let let  inlet  in in [hVbox0 1 5 1 [string fhead; formatHead (index,  , psi'',  , s,  , psi); space; string "="; break; formatPro3 (psi'',  , p)]; break] formatPro2(index,  , psi,  , (psi',  , s,  , p) :: o) let let  in in formatPro2 (index,  , psi,  , o) @ [hVbox0 1 5 1 [string "  |"; formatHead (index,  , psi'',  , s,  , psi); space; string "="; break; formatPro3 (psi'',  , p)]; break](* formatPro1 (index, Psi, P) = fmts'

           Invariant:
           If   |- Psi ctx
           and  Psi; . |- P :: F
           and  P is either a Lam .. | Case ... | Pair ...
           then fmts' is alist of pretty print formats of P
        *)
let rec formatPro1(index,  , psi,  , lam (d,  , p)) formatPro1 (index,  , decl (psi,  , decName (makectx psi,  , d)),  , p) formatPro1(index,  , psi,  , case (opts os)) formatPro2 (index,  , psi,  , os) formatPro1(index,  , psi,  , pair (p1,  , p2)) formatPro1 (index,  , psi,  , p1) @ formatPro1 (index + 1,  , psi,  , p2)(* formatPro0 (Psi, P) = fmt'
           If   |- Psi ctx
           and  Psi; . |- P :: F
           then fmt' is a pretty print format of P
        *)
let rec formatPro0(psi,  , rec (dD,  , p)) vbox0 0 1 (formatPro1 (0,  , psi,  , p)) in (varReset null; formatPro0 args)let rec formatLemmaDec(lemmaDec (names,  , p,  , f)) vbox0 0 1 [formatFor (null,  , f) names; break; formatPro (null,  , p) names]let rec forToStringargsnames makestring_fmt (formatFor args names)let rec proToStringargsnames makestring_fmt (formatPro args names)let rec lemmaDecToStringargs makestring_fmt (formatLemmaDec args)let  inlet  inlet  inlet  inlet  inlet  inlet  inend