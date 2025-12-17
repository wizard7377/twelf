Splitting  Global GLOBAL    MetaSyn' METASYN    MetaAbstract METAABSTRACT    MetaPrint METAPRINT    MetaPrint MetaSyn  MetaSyn'   MetaAbstract MetaSyn  MetaSyn'   ModeTable MODETABLE    Whnf WHNF    Index INDEX    Print PRINT    Unify UNIFY     SPLITTING  struct module exception (* Invariant:
     Case analysis generates a list of successor states
     (the cases) from a given state.

     'a flag marks cases where unification of the types
     succeeded as "Active", and cases where there were
     leftover constraints after unification as "Inactive".

     NB: cases where unification fails are not considered

     Consequence: Only those splitting operators can be
     applied which do not generate inactive cases.
  *)
type Flagtype Operatormodule module (* constCases (G, (V, s), I, abstract, C) = C'

       Invariant:
       If   G |- s : G'  G' |- V : type
       and  I a list of of constant declarations
       and  abstract an abstraction function
       and  C a list of possible cases
       then C' is a list extending C, containing all possible
         cases from I
    *)
let rec constCases(g,  , vs,  , nil,  , abstract,  , ops) ops constCases(g,  , vs,  , const c :: sgn,  , abstract,  , ops) let let  in in constCases (g,  , vs,  , sgn,  , abstract,  , trail (fun () -> try  with ))(* paramCases (G, (V, s), k, abstract, C) = C'

       Invariant:
       If   G |- s : G'  G' |- V : type
       and  k a variable
       and  abstract an abstraction function
       and  C a list of possible cases
       then C' is a list extending C, containing all possible
         cases introduced by parameters <= k in G
    *)
let rec paramCases(g,  , vs,  , 0,  , abstract,  , ops) ops paramCases(g,  , vs,  , k,  , abstract,  , ops) let let  in in paramCases (g,  , vs,  , k - 1,  , abstract,  , trail (fun () -> try  with ))(* lowerSplitDest (G, (V, s'), abstract) = C'

       Invariant:
       If   G0, G |- s' : G1  G1 |- V: type
       and  G is the context of local parameters
       and  abstract abstraction function
       then C' is a list of all cases unifying with V[s']
            (it contains constant and parameter cases)
    *)
let rec lowerSplitDest(g,  , (v as root (const c,  , _),  , s'),  , abstract) constCases (g,  , (v,  , s'),  , lookup c,  , abstract,  , paramCases (g,  , (v,  , s'),  , ctxLength g,  , abstract,  , nil)) lowerSplitDest(g,  , (pi ((d,  , p),  , v),  , s'),  , abstract) let let  in in lowerSplitDest (decl (g,  , d'),  , (v,  , dot1 s'),  , fun (name,  , u) -> abstract (name,  , lam (d',  , u)))(* split ((G, M), (x:D, s), abstract) = C'

       Invariant :
       If   |- G ctx
       and  G |- M mtx
       and  G |- s : G1   and  G1 |- D : L
       and  abstract abstraction function
       then C' = (C1, ... Cn) are resulting cases from splitting D[s]
    *)
let rec split(prefix (g,  , m,  , b),  , (d as dec (_,  , v),  , s),  , abstract) lowerSplitDest (null,  , (v,  , s),  , fun (name',  , u') -> abstract (name',  , prefix (g,  , m,  , b),  , dot (exp (u'),  , s)))(* rename to add N prefix? *)
(* occursIn (k, U) = B,

       Invariant:
       If    U in nf
       then  B iff k occurs in U
    *)
let rec occursInExp(k,  , uni _) false occursInExp(k,  , pi (dP,  , v)) occursInDecP (k,  , dP) || occursInExp (k + 1,  , v) occursInExp(k,  , root (c,  , s)) occursInCon (k,  , c) || occursInSpine (k,  , s) occursInExp(k,  , lam (d,  , v)) occursInDec (k,  , d) || occursInExp (k + 1,  , v) occursInExp(k,  , fgnExp csfe) fold csfe (fun (u,  , b) -> b || occursInExp (k,  , normalize (u,  , id))) false(* no case for Redex, EVar, EClo *)
 occursInCon(k,  , bVar (k')) (k = k') occursInCon(k,  , const _) false occursInCon(k,  , def _) false occursInCon(k,  , skonst _) false(* no case for FVar *)
 occursInSpine(_,  , nil) false occursInSpine(k,  , app (u,  , s)) occursInExp (k,  , u) || occursInSpine (k,  , s)(* no case for SClo *)
 occursInDec(k,  , dec (_,  , v)) occursInExp (k,  , v) occursInDecP(k,  , (d,  , _)) occursInDec (k,  , d)let rec isIndexInitk falselet rec isIndexSucc(d,  , isIndex)k occursInDec (k,  , d) || isIndex (k + 1)let rec isIndexFail(d,  , isIndex)k isIndex (k + 1)(* checkExp (M, U) = B

       Invariant:
       If   G |- M
       and  G |- U : V
       and  U in nf
       then B holds iff U does not contain any Bot variables
    *)
let rec checkVar(decl (m,  , top),  , 1) true checkVar(decl (m,  , bot),  , 1) false checkVar(decl (m,  , _),  , k) checkVar (m,  , k - 1)let rec checkExp(m,  , uni _) true checkExp(m,  , pi ((d,  , p),  , v)) checkDec (m,  , d) && checkExp (decl (m,  , top),  , v) checkExp(m,  , lam (d,  , v)) checkDec (m,  , d) && checkExp (decl (m,  , top),  , v) checkExp(m,  , root (bVar k,  , s)) checkVar (m,  , k) && checkSpine (m,  , s) checkExp(m,  , root (_,  , s)) checkSpine (m,  , s) checkSpine(m,  , nil) true checkSpine(m,  , app (u,  , s)) checkExp (m,  , u) && checkSpine (m,  , s) checkDec(m,  , dec (_,  , v)) checkExp (m,  , v)(* copied from meta-abstract *)
(* modeEq (marg, st) = B'

       Invariant:
       If   (marg = + and st = top) or (marg = - and st = bot)
       then B' = true
       else B' = false
    *)
let rec modeEq(marg (plus,  , _),  , top) true modeEq(marg (minus,  , _),  , bot) true modeEq_ false(*
       The inherit functions below copy the splitting depth attribute
       between successive states, using a simultaneous traversal
       in mode dependency order.

       Invariant:
       (G,M,B) |- V type
       G = G0, G1, G2
       |G2| = k       (length of local context)
       d = |G1, G2|   (last BVar seen)
       let n < |G|
       if   n>d then n is an index of a variable already seen in mdo
       if   n=d then n is an index of a variable now seen for the first
                     time
       if   n<=k then n is a local parameter
       it is impossible for     k < n < d
    *)
(* invariants on inheritXXX functions? -fp *)
let rec inheritBelow(b',  , k',  , lam (d',  , u'),  , bdd') inheritBelow (b',  , k' + 1,  , u',  , inheritBelowDec (b',  , k',  , d',  , bdd')) inheritBelow(b',  , k',  , pi ((d',  , _),  , v'),  , bdd') inheritBelow (b',  , k' + 1,  , v',  , inheritBelowDec (b',  , k',  , d',  , bdd')) inheritBelow(b',  , k',  , root (bVar (n'),  , s'),  , (b',  , d,  , d')) if n' = k' + d' && n' > k'(* necessary for d' = 0 *)
 then inheritBelowSpine (b',  , k',  , s',  , (decl (b',  , b'),  , d,  , d' - 1)) else inheritBelowSpine (b',  , k',  , s',  , (b',  , d,  , d')) inheritBelow(b',  , k',  , root (c,  , s'),  , bdd') inheritBelowSpine (b',  , k',  , s',  , bdd') inheritBelowSpine(b',  , k',  , nil,  , bdd') bdd' inheritBelowSpine(b',  , k',  , app (u',  , s'),  , bdd') inheritBelowSpine (b',  , k',  , s',  , inheritBelow (b',  , k',  , u',  , bdd')) inheritBelowDec(b',  , k',  , dec (x,  , v'),  , bdd') inheritBelow (b',  , k',  , v',  , bdd')(* skip *)
let rec skip(k,  , lam (d,  , u),  , bdd') skip (k + 1,  , u,  , skipDec (k,  , d,  , bdd')) skip(k,  , pi ((d,  , _),  , v),  , bdd') skip (k + 1,  , v,  , skipDec (k,  , d,  , bdd')) skip(k,  , root (bVar (n),  , s),  , (b',  , d,  , d')) if n = k + d && n > k(* necessary for d = 0 *)
 then skipSpine (k,  , s,  , (b',  , d - 1,  , d')) else skipSpine (k,  , s,  , (b',  , d,  , d')) skip(k,  , root (c,  , s),  , bdd') skipSpine (k,  , s,  , bdd') skipSpine(k,  , nil,  , bdd') bdd' skipSpine(k,  , app (u,  , s),  , bdd') skipSpine (k,  , s,  , skip (k,  , u,  , bdd')) skipDec(k,  , dec (x,  , v),  , bdd') skip (k,  , v,  , bdd')(* Uni impossible *)
let rec inheritExp(b,  , k,  , lam (d,  , u),  , k',  , lam (d',  , u'),  , bdd') inheritExp (b,  , k + 1,  , u,  , k' + 1,  , u',  , inheritDec (b,  , k,  , d,  , k',  , d',  , bdd')) inheritExp(b,  , k,  , pi ((d,  , _),  , v),  , k',  , pi ((d',  , _),  , v'),  , bdd') inheritExp (b,  , k + 1,  , v,  , k' + 1,  , v',  , inheritDec (b,  , k,  , d,  , k',  , d',  , bdd')) inheritExp(b,  , k,  , v as root (bVar (n),  , s),  , k',  , v',  , (b',  , d,  , d')) if n = k + d && n > k(* new original variable *)
 then (* inheritBelow (I.ctxLookup (B, n-k) - 1, k', V', (B', d-1, d')) *)
skipSpine (k,  , s,  , inheritNewRoot (b,  , ctxLookup (b,  , n - k),  , k,  , v,  , k',  , v',  , (b',  , d,  , d'))) else if n > k + d(* already seen original variable *)
(* then (B', d, d') *)
(* previous line avoids redundancy,
                  but may violate invariant outside pattern fragment *)
 then skipSpine (k,  , s,  , inheritBelow (ctxLookup (b,  , n - k) - 1,  , k',  , v',  , (b',  , d,  , d'))) else (* must correspond *)
let let  in(* C' = BVar (n) *)
 in inheritSpine (b,  , k,  , s,  , k',  , s',  , (b',  , d,  , d')) inheritExp(b,  , k,  , root (c,  , s),  , k',  , root (c',  , s'),  , bdd') inheritSpine (b,  , k,  , s,  , k',  , s',  , bdd') inheritNewRoot(b,  , b,  , k,  , root (bVar (n),  , s),  , k',  , v' as root (bVar (n'),  , s'),  , (b',  , d,  , d')) if n' = k' + d' && n' > k'(* n' also new --- same variable: do not decrease *)
 then inheritBelow (b,  , k',  , v',  , (b',  , d - 1,  , d')) else inheritBelow (b - 1,  , k',  , v',  , (b',  , d - 1,  , d')) inheritNewRoot(b,  , b,  , k,  , v,  , k',  , v',  , (b',  , d,  , d')) inheritBelow (b - 1,  , k',  , v',  , (b',  , d - 1,  , d')) inheritSpine(b,  , k,  , nil,  , k',  , nil,  , bdd') bdd' inheritSpine(b,  , k,  , app (u,  , s),  , k',  , app (u',  , s'),  , bdd') inheritSpine (b,  , k,  , s,  , k',  , s',  , inheritExp (b,  , k,  , u,  , k',  , u',  , bdd')) inheritDec(b,  , k,  , dec (_,  , v),  , k',  , dec (_,  , v'),  , bdd') inheritExp (b,  , k,  , v,  , k',  , v',  , bdd')let rec inheritDTop(b,  , k,  , pi ((dec (_,  , v1),  , no),  , v2),  , k',  , pi ((dec (_,  , v1'),  , no),  , v2'),  , bdd') inheritG (b,  , k,  , v1,  , k',  , v1',  , inheritDTop (b,  , k + 1,  , v2,  , k' + 1,  , v2',  , bdd')) inheritDTop(b,  , k,  , v as root (const (cid),  , s),  , k',  , v' as root (const (cid'),  , s'),  , bdd') let let  in in inheritSpineMode (top,  , mS,  , b,  , k,  , s,  , k',  , s',  , bdd') inheritDBot(b,  , k,  , pi ((dec (_,  , v1),  , no),  , v2),  , k',  , pi ((dec (_,  , v1'),  , no),  , v2'),  , bdd') inheritDBot (b,  , k + 1,  , v2,  , k' + 1,  , v2',  , bdd') inheritDBot(b,  , k,  , root (const (cid),  , s),  , k',  , root (const (cid'),  , s'),  , bdd') let let  in in inheritSpineMode (bot,  , mS,  , b,  , k,  , s,  , k',  , s',  , bdd') inheritG(b,  , k,  , root (const (cid),  , s),  , k',  , v' as root (const (cid'),  , s'),  , bdd') let let  in in (* mode dependency in Goal: first M.Top, then M.Bot *)
inheritSpineMode (bot,  , mS,  , b,  , k,  , s,  , k',  , s',  , inheritSpineMode (top,  , mS,  , b,  , k,  , s,  , k',  , s',  , bdd')) inheritSpineMode(mode,  , mnil,  , b,  , k,  , nil,  , k',  , nil,  , bdd') bdd' inheritSpineMode(mode,  , mapp (m,  , mS),  , b,  , k,  , app (u,  , s),  , k',  , app (u',  , s'),  , bdd') if modeEq (m,  , mode) then inheritSpineMode (mode,  , mS,  , b,  , k,  , s,  , k',  , s',  , inheritExp (b,  , k,  , u,  , k',  , u',  , bdd')) else inheritSpineMode (mode,  , mS,  , b,  , k,  , s,  , k',  , s',  , bdd')let rec inheritSplitDepth(s as state (_,  , prefix (g,  , m,  , b),  , v),  , s' as state (name',  , prefix (g',  , m',  , b'),  , v')) let let  in(* current first occurrence depth in V *)
let  in(* current first occurrence depth in V' *)
(* mode dependency in Clause: first M.Top then M.Bot *)
(* check proper traversal *)
let  inlet  inlet  in in state (name',  , prefix (g',  , m',  , b''),  , v')(* abstractInit (M.State (name, M.Prefix (G, M, B), V)) = F'

       State is the state before splitting, to inherit splitting depths.
       Invariant:
       If   G |- V : L
       then forall |- G' ctx
            and    G' |- M' ctx
            and    G' |- s' : G
            and    names name'
            then   following holds: S' = F' (name', G', M', s')
                                    S' is a new state
    *)
let rec abstractInit(state (name,  , gM,  , v))(name',  , prefix (g',  , m',  , b'),  , s') inheritSplitDepth (state (name,  , gM,  , v),  , abstract (state (name ^ name',  , prefix (g',  , m',  , b'),  , eClo (v,  , s'))))(* abstractInit (x:D, mode, F) = F'

       Invariant:
       If   G |- D : L
       and  forall |- G' ctx
            and    G' |- M' ctx
            and    G' |- s' : G
            and    names name'
            then   S' = F (name', G', M', s')
       then forall |- G' ctx
            and    G' |- M' ctx
            and    G' |- s' : G
            then   following holds: S' = F (name', (G', D[s]) , (M', mode) , 1 . s' o ^)
                                    is a new state
    *)
let rec abstractCont((d,  , mode,  , b),  , abstract)(name',  , prefix (g',  , m',  , b'),  , s') abstract (name',  , prefix (decl (g',  , decSub (d,  , s')),  , decl (m',  , mode),  , decl (b',  , b)),  , dot1 s')let rec makeAddressInitsk (s,  , k)let rec makeAddressContmakeAddressk makeAddress (k + 1)(* expand' (M.Prefix (G, M), isIndex, abstract, makeAddress) = (M.Prefix (G', M'), s', ops')

       Invariant:
       If   |- G ctx
       and  G |- M mtx
       and  isIndex (k) = B function s.t. B holds iff k index
       and  abstract, dynamic abstraction function
       and  makeAddress, a function which calculates the index of the variable
            to be split
       then |- G' ctx
       and  G' |- M' mtx
       and  G' is a subcontext of G where all Top variables have been replaced
            by EVars'
       and  G' |- s' : G
       and  ops' is a list of all possiblie splitting operators
    *)
let rec expand'(prefix (null,  , null,  , null),  , isIndex,  , abstract,  , makeAddress) (prefix (null,  , null,  , null),  , id,  , nil) expand'(prefix (decl (g,  , d),  , decl (m,  , mode as top),  , decl (b,  , b)),  , isIndex,  , abstract,  , makeAddress) let let  inlet  inlet  inlet  in in (prefix (g',  , m',  , b'),  , dot (exp (x),  , s'),  , ops') expand'(prefix (decl (g,  , d),  , decl (m,  , mode as bot),  , decl (b,  , b)),  , isIndex,  , abstract,  , makeAddress) let let  in in (prefix (decl (g',  , decSub (d,  , s')),  , decl (m',  , bot),  , decl (b',  , b)),  , (* b = 0 *)
, dot1 s',  , ops)(* expand ((G, M), V) = ops'

       Invariant:
       If   |- G ctx
       and  G |- M mtx
       and  G |- V : L
       then ops' is a list of all possiblie splitting operators
    *)
let rec expand(s as state (name,  , prefix (g,  , m,  , b),  , v)) let let  in in ops(* index (Op) = k

       Invariant:
       If   Op = (_, S) then k = |S|
    *)
let rec index(_,  , sl) length sl(* apply (Op) = Sl'

       Invariant:
       If   Op = (_, Sl) then Sl' = Sl
    *)
let rec apply(_,  , sl) map (fun (active s) -> s inActive -> raise (error "Not applicable: leftover constraints")) sl(* menu (Op) = s'

       Invariant:
       If   Op = ((G, D), Sl)
       and  G |- D : L
       then s' = string describing the operator
    *)
let rec menu(op as ((state (name,  , prefix (g,  , m,  , b),  , v),  , i),  , sl)) let let rec active(nil,  , n) n active(inActive :: l,  , n) active (l,  , n) active((active _) :: l,  , n) active (l,  , n + 1)let rec inactive(nil,  , n) n inactive(inActive :: l,  , n) inactive (l,  , n + 1) inactive((active _) :: l,  , n) inactive (l,  , n)let rec indexToString0 "zero cases" indexToString1 "1 case" indexToStringn (toString n) ^ " cases"let rec flagToString(_,  , 0) "" flagToString(n,  , m) " [active: " ^ (toString n) ^ " inactive: " ^ (toString m) ^ "]" in "Splitting : " ^ decToString (g,  , ctxDec (g,  , i)) ^ " (" ^ (indexToString (index op)) ^ (flagToString (active (sl,  , 0),  , inactive (sl,  , 0))) ^ ")"let rec var((_,  , i),  , _) ilet  inlet  inlet  inlet  inlet  in(* local *)
end