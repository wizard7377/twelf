AbstractTabled  Whnf WHNF    Unify UNIFY    Constraints CONSTRAINTS    Subordinate SUBORDINATE    Print PRINT    Conv CONV     ABSTRACTTABLED  struct (*! structure IntSyn = IntSyn' !*)
(*! structure TableParam = TableParam !*)
exception module module type Duplicatestype SeenIntype ExistVarslet rec lengthSub(shift n) 0 lengthSub(dot (e,  , s)) 1 + lengthSub s(*
       We write {{K}} for the context of K, where EVars have
       been translated to declarations and their occurrences to BVars.
       For each occurrence of EVar in U, we generate a distinct BVar together with
       a residual constraint. This enforces that the final abstraction of U is
       linear. However, we do not linearize the context G.

       We write {{U}}_K, {{S}}_K for the corresponding translation of an
       expression or spine.

       Just like contexts G, any K is implicitly assumed to be
       well-formed and in dependency order.

       We write  K ||- U  if all EVars in U are collected in K.
       In particular, . ||- U means U contains no EVars.  Similarly,
       for spines K ||- S and other syntactic categories.

       Collection and abstraction raise Error if there are unresolved
       constraints after simplification.
    *)
let rec compose'(null,  , g) g compose'(decl (g',  , d),  , g) decl (compose' (g',  , g),  , d)let rec isId(shift (n)) (n = 0) isId(s as dot (idx n,  , s')) isId' (s,  , 0) isId(s as dot (undef,  , s')) isId' (s,  , 0) isId(dot (exp _,  , s)) false isId'(shift (n),  , k) (n = k) isId'(dot (idx (i),  , s),  , k) let let  in in (i = k') && isId' (s,  , k') isId'(dot (undef,  , s),  , k) isId' (s,  , k + 1)let rec equalCtx(null,  , s,  , null,  , s') true equalCtx(decl (g,  , d),  , s,  , decl (g',  , d'),  , s') convDec ((d,  , s),  , (d',  , s')) && (equalCtx (g,  , dot1 s,  , g',  , dot1 s')) equalCtx(decl (g,  , d),  , s,  , null,  , s') false equalCtx(null,  , s,  , decl (g',  , d'),  , s') false(* eqEVar X Y = B
     where B iff X and Y represent same variable
     *)
let rec eqEVarW(eVar (r1,  , _,  , _,  , _))(eV (eVar (r2,  , _,  , _,  , _))) (r1 = r2) eqEVarW__ falselet rec eqEVarx1(eV (x2)) let let  inlet  in in eqEVarW x1' (eV (x2'))(* a few helper functions to manage K *)
(* member P K = B option *)
let rec member'pk let let rec exists'(null) nONE exists'(decl (k',  , (l,  , eV (y)))) if p (eV (y)) then sOME (l) else exists' (k') in exists' k(* member P K = B option *)
let rec memberpk let let rec exists'(null) nONE exists'(decl (k',  , (i,  , y))) if p (y) then sOME (i) else exists' (k') in exists' klet rec update'pk let let rec update'(null) null update'(decl (k',  , ((label,  , y)))) if (p y) then decl (k',  , (body,  , y)) else decl (update' (k'),  , (label,  , y)) in update' k(* member P K = B option *)
let rec updatepk let let rec update'(null) null update'(decl (k',  , ((label,  , i),  , y))) if (p y) then decl (k',  , ((body,  , i),  , y)) else decl (update' (k'),  , ((label,  , i),  , y)) in update' klet rec or(maybe,  , _) maybe or(_,  , maybe) maybe or(meta,  , _) meta or(_,  , meta) meta or(no,  , no) no(* occursInExp (k, U) = DP,

       Invariant:
       If    U in nf
       then  DP = No      iff k does not occur in U
             DP = Maybe   iff k occurs in U some place not as an argument to a Skonst
             DP = Meta    iff k occurs in U and only as arguments to Skonsts
    *)
let rec occursInExp(k,  , uni _) no occursInExp(k,  , pi (dP,  , v)) or (occursInDecP (k,  , dP),  , occursInExp (k + 1,  , v)) occursInExp(k,  , root (h,  , s)) occursInHead (k,  , h,  , occursInSpine (k,  , s)) occursInExp(k,  , lam (d,  , v)) or (occursInDec (k,  , d),  , occursInExp (k + 1,  , v)) occursInExp(k,  , fgnExp csfe) fold csfe (fun (u,  , dP) -> or (dP,  , (occursInExp (k,  , normalize (u,  , id))))) no(* no case for Redex, EVar, EClo *)
 occursInHead(k,  , bVar (k'),  , dP) if (k = k') then maybe else dP occursInHead(k,  , const _,  , dP) dP occursInHead(k,  , def _,  , dP) dP occursInHead(k,  , fgnConst _,  , dP) dP occursInHead(k,  , skonst _,  , no) no occursInHead(k,  , skonst _,  , meta) meta occursInHead(k,  , skonst _,  , maybe) meta(* no case for FVar *)
 occursInSpine(_,  , nil) no occursInSpine(k,  , app (u,  , s)) or (occursInExp (k,  , u),  , occursInSpine (k,  , s))(* no case for SClo *)
 occursInDec(k,  , dec (_,  , v)) occursInExp (k,  , v) occursInDecP(k,  , (d,  , _)) occursInDec (k,  , d)(* piDepend ((D,P), V) = Pi ((D,P'), V)
       where P' = Maybe if D occurs in V, P' = No otherwise
    *)
(* optimize to have fewer traversals? -cs *)
(* pre-Twelf 1.2 code walk Fri May  8 11:17:10 1998 *)
let rec piDepend(dPV as ((d,  , no),  , v)) pi dPV piDepend(dPV as ((d,  , meta),  , v)) pi dPV piDepend((d,  , maybe),  , v) pi ((d,  , occursInExp (1,  , v)),  , v)(* raiseType (G, V) = {{G}} V

       Invariant:
       If G |- V : L
       then  . |- {{G}} V : L

       All abstractions are potentially dependent.
    *)
let rec raiseType(null,  , v) v raiseType(decl (g,  , d),  , v) raiseType (g,  , pi ((d,  , maybe),  , v))let rec reverseCtx(null,  , g) g reverseCtx(decl (g,  , d),  , g') reverseCtx (g,  , decl (g',  , d))let rec ctxToEVarSub(null,  , s) s ctxToEVarSub(decl (g,  , dec (_,  , a)),  , s) let let  inlet  in in dot (exp (x),  , s')(* collectExpW ((Gs, ss), Gl, (U, s), K, DupVars, flag) = (K', DupVars')

       Invariant:
       If    G, Gl |- s : G1     G1 |- U : V      (U,s) in whnf
                Gs |- ss : G  (Gs is the strengthened context and ss is the strengthening substitution)

       No circularities in U
             (enforced by extended occurs-check for FVars in Unify)
       and   K' = K, K''
             where K' contains all EVars in (U,s)
       and  DupVars' = DupVars, DupVars''
            where DupVars' contains all duplicates in (U,s)

      if flag = true
        then duplicates of EVars are collected in DupVars
        otherwise no duplicates are collected

      note : 1) we only need to collect duplicate occurrences of EVars
                if we need to linearize the term the EVars occur in.

             2) we do not linearize fgnExp
    *)
(* Possible optimization: Calculate also the normal form of the term *)
let rec collectExpW(gss,  , gl,  , (uni l,  , s),  , k,  , dupVars,  , flag,  , d) (k,  , dupVars) collectExpW(gss,  , gl,  , (pi ((d,  , _),  , v),  , s),  , k,  , dupVars,  , flag,  , d) let let  in in (* should we apply I.dot1(ss) ? Tue Oct 15 21:55:16 2002 -bp *)
collectExp (gss,  , decl (gl,  , decSub (d,  , s)),  , (v,  , dot1 s),  , k',  , dupVars,  , flag,  , d) collectExpW(gss,  , gl,  , (root (_,  , s),  , s),  , k,  , dupVars,  , flag,  , d) collectSpine (gss,  , gl,  , (s,  , s),  , k,  , dupVars,  , flag,  , d) collectExpW(gss,  , gl,  , (lam (d,  , u),  , s),  , k,  , dupVars,  , flag,  , d) let let  in in collectExp (gss,  , decl (gl,  , decSub (d,  , s)),  , (u,  , dot1 s),  , k',  , dupVars,  , flag,  , d + 1) collectExpW(gss,  , gl,  , (x as eVar (r,  , gX,  , v,  , cnstrs),  , s),  , k,  , dupVars,  , flag,  , d) collectEVar (gss,  , gl,  , (x,  , s),  , k,  , dupVars,  , flag,  , d) collectExpW(gss,  , gl,  , (fgnExp csfe,  , s),  , k,  , dupVars,  , flag,  , d) fold csfe (fun (u,  , kD') -> let let  in in collectExp (gss,  , gl,  , (u,  , s),  , k',  , dup,  , false,  , d)) (k,  , decl (dupVars,  , fGN (d)))(* No other cases can occur due to whnf invariant *)
(* collectExp (Gss, G, Gl, (U, s), K) = K'
       same as collectExpW  but  (U,s) need not to be in whnf
    *)
 collectExp(gss,  , gl,  , us,  , k,  , dupVars,  , flag,  , d) collectExpW (gss,  , gl,  , whnf us,  , k,  , dupVars,  , flag,  , d)(* collectSpine (Gss, Gl, (S, s), K, DupVars, flag) = (K', DupVars')

       Invariant:
       If    G, Gl |- s : G1     G1 |- S : V > P
                Gs |- ss : G
       then  K' = K, K'' and DupVars' = DupVars, DupVars''
       where K'' contains all EVars in (S, s)
       and DupVars'' contains all duplicates in (S, s)
     *)
 collectSpine(gss,  , gl,  , (nil,  , _),  , k,  , dupVars,  , flag,  , d) (k,  , dupVars) collectSpine(gss,  , gl,  , (sClo (s,  , s'),  , s),  , k,  , dupVars,  , flag,  , d) collectSpine (gss,  , gl,  , (s,  , comp (s',  , s)),  , k,  , dupVars,  , flag,  , d) collectSpine(gss,  , gl,  , (app (u,  , s),  , s),  , k,  , dupVars,  , flag,  , d) let let  in in collectSpine (gss,  , gl,  , (s,  , s),  , k',  , dupVars',  , flag,  , d) collectEVarFapStr(gss,  , gl,  , ((x',  , v'),  , w),  , (x as eVar (r,  , gX,  , v,  , cnstrs),  , s),  , k,  , dupVars,  , flag,  , d) match member' (eqEVar x) k with sOME (label) -> (* we have seen X before *)
(if flag then collectSub (gss,  , gl,  , s,  , k,  , decl (dupVars,  , aV (x,  , d)),  , flag,  , d)(* case label of
                     Body => collectSub(Gss, Gl, s, K, I.Decl(DupVars, AV(X,d)), flag, d)
                   | TypeLabel =>
                       let
                         val K' = update' (eqEVar X) K
                       in
                         collectSub(Gss, Gl, s, K', DupVars, flag, d)
                       end *)
(* since X has occurred before, we do not traverse its type V' *)
 else collectSub (gss,  , gl,  , s,  , k,  , dupVars,  , flag,  , d)) nONE -> let (*          val V' = raiseType (GX, V) (* inefficient! *)*)
let  inlet  in in collectSub (gss,  , gl,  , comp (w,  , s),  , decl (k',  , (label,  , eV (x'))),  , dupVars',  , flag,  , d) collectEVarNFapStr(gss,  , gl,  , ((x',  , v'),  , w),  , (x as eVar (r,  , gX,  , v,  , cnstrs),  , s),  , k,  , dupVars,  , flag,  , d) match member' (eqEVar x) k with sOME (label) -> (* we have seen X before, i.e. it was already strengthened *)
(if flag then collectSub (gss,  , gl,  , s,  , k,  , decl (dupVars,  , aV (x,  , d)),  , flag,  , d)(* -bp this is a possible optimization for the variant case
                   case label of
                   Body => (print "Collect DupVar\n"; collectSub(Gss, Gl, s, K, I.Decl(DupVars, AV(X, d)), flag, d) )
                 | TypeLabel =>
                    let
                      val _ = print "TypeLabel\n"
                      val K' = update' (eqEVar X) K
                    in
                      collectSub(Gss, Gl, s, K', DupVars, flag, d)
                    end*)
 else collectSub (gss,  , gl,  , s,  , k,  , dupVars,  , flag,  , d)) nONE -> let (* val V' = raiseType (GX, V) (* inefficient! *)*)
let  inlet  in in if flag then collectSub (gss,  , gl,  , comp (w,  , s),  , decl (k',  , (label,  , eV (x'))),  , decl (dupVars',  , aV (x',  , d)),  , flag,  , d) else collectSub (gss,  , gl,  , comp (w,  , s),  , decl (k',  , (label,  , eV (x'))),  , dupVars',  , flag,  , d) collectEVarStr(gss as (gs,  , ss),  , gl,  , (x as eVar (r,  , gX,  , v,  , cnstrs),  , s),  , k,  , dupVars,  , flag,  , d) let let  inlet  inlet  inlet  in(* ? *)
let  inlet  in in if isId (comp (w,  , comp (ss,  , s)))(* equalCtx (Gs, I.id, GX', s) *)
 then (* fully applied *)
collectEVarFapStr (gss,  , gl,  , ((x',  , v'),  , w),  , (x,  , s),  , k,  , dupVars,  , flag,  , d) else (* not fully applied *)
collectEVarNFapStr (gss,  , gl,  , ((x',  , v'),  , w),  , (x,  , s),  , k,  , dupVars,  , flag,  , d)(* X is fully applied pattern *)
 collectEVarFap(gss,  , gl,  , (x as eVar (r,  , gX,  , v,  , cnstrs),  , s),  , k,  , dupVars,  , flag,  , d) match (member (eqEVar x) k) with sOME (label) -> (* we have seen X before *)
(if flag then collectSub (gss,  , gl,  , s,  , k,  , decl (dupVars,  , aV (x,  , d)),  , flag,  , d)(*
                 case label of
                   Body => collectSub(Gss, Gl, s, K, I.Decl(DupVars, AV(X, d)), flag, d)
                 | TypeLabel =>
                     let
                       val K' = update' (eqEVar X) K
                     in
                       collectSub(Gss, Gl, s, K', DupVars, flag, d)
                     end *)
(* since X has occurred before, we do not traverse its type V' *)
 else collectSub (gss,  , gl,  , s,  , k,  , dupVars,  , flag,  , d)) nONE -> let (* val _ = checkEmpty !cnstrs *)
let  inlet  in(* inefficient! *)
let  in in collectSub (gss,  , gl,  , s,  , decl (k',  , (label,  , eV (x))),  , dupVars',  , flag,  , d) collectEVarNFap(gss,  , gl,  , (x as eVar (r,  , gX,  , v,  , cnstrs),  , s),  , k,  , dupVars,  , flag,  , d) match member' (eqEVar x) k with sOME (label) -> (if flag then collectSub (gss,  , gl,  , s,  , k,  , decl (dupVars,  , aV (x,  , d)),  , flag,  , d)(* case label of
                   Body => collectSub(Gss, Gl, s, K, I.Decl(DupVars, AV(X, d)), flag, d)
                   | TypeLabel =>
                     let
                       val K' = update' (eqEVar X) K
                     in
                       collectSub(Gss, Gl, s, K', DupVars, flag, d)
                     end             *)
 else collectSub (gss,  , gl,  , s,  , k,  , dupVars,  , flag,  , d)) nONE -> let let  inlet  in(* inefficient! *)
let  in in if flag then collectSub (gss,  , gl,  , s,  , decl (k',  , (label,  , eV (x))),  , decl (dupVars,  , aV (x,  , d)),  , flag,  , d) else collectSub (gss,  , gl,  , s,  , decl (k',  , (label,  , eV (x))),  , dupVars,  , flag,  , d) collectEVar(gss,  , gl,  , (x as eVar (r,  , gX,  , v,  , cnstrs),  , s),  , k,  , dupVars,  , flag,  , d) if (! strengthen) then collectEVarStr (gss,  , gl,  , (x,  , s),  , k,  , dupVars,  , flag,  , d) else if isId (s)(* equalCtx (compose'(Gl, G), s, GX, s)  *)
 then (* X is fully applied *)
collectEVarFap (gss,  , gl,  , (x,  , s),  , k,  , dupVars,  , flag,  , d) else (* X is not fully applied *)
collectEVarNFap (gss,  , gl,  , (x,  , s),  , k,  , dupVars,  , flag,  , d)(* collectDec (Gss, G, (x:V, s), K, DupVars, flag) = (K', DupVars')

       Invariant:
       If    G |- s : G1     G1 |- V : L
            Gs |- ss : G
       then  K' = K, K'' and DupVars' = DupVars, DupVars''
       where K'' contains all EVars in (V, s)
       and DupVars'' contains all duplicates in (S, s)
    *)
 collectDec(gss,  , (dec (_,  , v),  , s),  , (k,  , dupVars),  , d,  , flag) let (*      val (K',DupVars') =  collectExp (Gss, I.Null, (V, s), K, I.Null, false, d)*)
let  in in (k',  , dupVars')(* collectSub (G, s, K, DupVars, flag) = (K', DupVars)

       Invariant:
       If    G |- s : G1

       then  K' = K, K'' and DupVars' = DupVars, DupVars''
       where K'' contains all EVars in s
       and DupVars'' contains all duplicates in s
    *)
 collectSub(gss,  , gl,  , shift _,  , k,  , dupVars,  , flag,  , d) (k,  , dupVars) collectSub(gss,  , gl,  , dot (idx _,  , s),  , k,  , dupVars,  , flag,  , d) collectSub (gss,  , gl,  , s,  , k,  , dupVars,  , flag,  , d) collectSub(gss,  , gl,  , dot (exp (x as eVar (ref (sOME u),  , _,  , _,  , _)),  , s),  , k,  , dupVars,  , flag,  , d) let let  in(* inefficient? *)
let  in in collectSub (gss,  , gl,  , s,  , k',  , dupVars',  , flag,  , d) collectSub(gss,  , gl,  , dot (exp (u as aVar (ref (sOME u'))),  , s),  , k,  , dupVars,  , flag,  , d) let let  in in collectSub (gss,  , gl,  , s,  , k',  , dupVars',  , flag,  , d) collectSub(gss,  , gl,  , dot (exp (eClo (u',  , s')),  , s),  , k,  , dupVars,  , flag,  , d) let let  in(* inefficient? *)
let  in in collectSub (gss,  , gl,  , s,  , k',  , dupVars',  , flag,  , d) collectSub(gss,  , gl,  , dot (exp (u),  , s),  , k,  , dupVars,  , flag,  , d) let let  in in collectSub (gss,  , gl,  , s,  , k',  , dupVars',  , flag,  , d) collectSub(gss,  , gl,  , dot (undef,  , s),  , k,  , dupVars,  , flag,  , d) collectSub (gss,  , gl,  , s,  , k,  , dupVars,  , flag,  , d)(* collectCtx (Gss, G0, G, K) = (K', DupVars)
       Invariant:
       If G0 |- G ctx,
       then G0' = G0,G
       and K' = K, K'' where K'' contains all EVars in G
    *)
let rec collectCtx(gss,  , dProg (null,  , null),  , (k,  , dupVars),  , d) (k,  , dupVars) collectCtx(gss,  , dProg (decl (g,  , d),  , decl (dPool,  , parameter)),  , (k,  , dupVars),  , d) let let  in in collectDec (gss,  , (d,  , id),  , (k',  , dupVars'),  , d - 1,  , false) collectCtx(gss,  , dProg (decl (g,  , d),  , decl (dPool,  , dec (r,  , s,  , ha))),  , (k,  , dupVars),  , d) let let  in in collectDec (gss,  , (d,  , id),  , (k',  , dupVars'),  , d - 1,  , false)(* abstractExpW (epos, apos, Vars, Gl, total, depth, (U, s), eqn) = (epos', apos', Vars', U', eqn')
      (abstraction and linearization of existential variables in (U,s))

       U' = {{U[s]}}_(K, Dup)

       Invariant:
       If     G, Gl |- U[s] : V and  U[s] is in whnf
       and   |Gl| = depth
             |Dup, K| = total

       and epos = (total(K) + l) - #replaced expressions in U    (generate no additional constraints)
       and apos = (total(Dup) + + total(K) + l) - #replaced expressions in U
                  (generate additional constraints (avars))

       and Vars'  = Vars, Vars''
           where Vars contains pairs ((label, i), EV X) of all EVars (EV X),
           where label refers to where we have seen the existential variable (typeLabel or body) and
           i corresponds to the bvar-index assigned to X in U[s]

       and   K ~ Vars (we can obtain K from Vars by dropping the first component of
             each pair (_, EV X) in Vars' )

       then   {{Dup}}, {{K}}  ||- U
       and {{Dup}} {{K}} , G, Gl |-  U' : V'
       and eqn' = eqn, eqn'' where eqn'' are residual equations relating between elements
           in {{K}} and {{Dup}}

       and . ||- Pi G. U'  and   U' is in nf

       if flag then linearize U else allow duplicates.

    *)
let rec abstractExpW(flag,  , gs,  , posEA,  , vars,  , gl,  , total,  , depth,  , (u as uni (l),  , s),  , eqn) (posEA,  , vars,  , u,  , eqn) abstractExpW(flag,  , gs,  , posEA,  , vars,  , gl,  , total,  , depth,  , (pi ((d,  , p),  , v),  , s),  , eqn) let let  inlet  in in (posEA'',  , vars'',  , piDepend ((d,  , p),  , v'),  , eqn2) abstractExpW(flag,  , gs,  , posEA,  , vars,  , gl,  , total,  , depth,  , (root (h,  , s),  , s),  , eqn) let let  in in (posEA',  , vars',  , root (h,  , s),  , eqn') abstractExpW(flag,  , gs,  , posEA,  , vars,  , gl,  , total,  , depth,  , (lam (d,  , u),  , s),  , eqn) let let  inlet  in in (posEA'',  , vars'',  , lam (d',  , u'),  , eqn2) abstractExpW(flag,  , gs as (gss,  , ss),  , posEA as (epos,  , apos),  , vars,  , gl,  , total,  , depth,  , (x as eVar (_,  , gX,  , vX,  , _),  , s),  , eqn) if isId (comp (ss,  , s)) then (* X is fully applied *)
abstractEVarFap (flag,  , gs,  , posEA,  , vars,  , gl,  , total,  , depth,  , (x,  , s),  , eqn) else (* s =/= id, i.e. X is not fully applied *)
abstractEVarNFap (flag,  , gs,  , posEA,  , vars,  , gl,  , total,  , depth,  , (x,  , s),  , eqn)(*      | abstractExpW (posEA, Vars, Gl, total, depth, (X as I.FgnExp (cs, ops), s), eqn) =  *)
(*      let
          val (X, _) = #map(ops) (fn U => abstractExp (posEA, Vars, Gl, total, depth, (U, s), eqn))
        in        abstractFgn (posEA, Vars, Gl, total, depth, X, eqn)
        end
*)
(* abstractExp (posEA, Vars, Gl, total, depth, (U, s)) = U'

       same as abstractExpW, but (U,s) need not to be in whnf
    *)
 abstractExp(flag,  , gs,  , posEA,  , vars,  , gl,  , total,  , depth,  , us,  , eqn) abstractExpW (flag,  , gs,  , posEA,  , vars,  , gl,  , total,  , depth,  , whnf us,  , eqn) abstractEVarFap(flag,  , gs,  , posEA as (epos,  , apos),  , vars,  , gl,  , total,  , depth,  , (x,  , s),  , eqn) match (member (eqEVar x) vars) with sOME (label,  , i) -> (* we have seen X before *)
if flag then (* enforce linearization *)
match label with body -> let let  inlet  inlet  inlet  in in (posEA',  , vars',  , root (bV,  , nil),  , unify (gl,  , root (bV',  , s),  , root (bV1,  , nil),  , eqn1)) typeLabel -> let let  inlet  in in (posEA',  , vars'',  , root (bVar (i + depth),  , s),  , eqn1) else (* do not enforce linearization -- used for type labels *)
let let  in in (posEA',  , vars',  , root (bVar (i + depth),  , s),  , eqn1) nONE -> (* we see X for the first time *)
let let  inlet  inlet  inlet  in in (posEA',  , vars',  , root (bV,  , s),  , eqn1) abstractEVarNFap(flag,  , gs,  , posEA as (epos,  , apos),  , vars,  , gl,  , total,  , depth,  , (x,  , s),  , eqn) match (member (eqEVar x) vars) with sOME (label,  , i) -> (* we have seen X before *)
if flag then (* enforce linearization *)
let let  inlet  inlet  inlet  in in (posEA',  , vars',  , root (bV,  , nil),  , unify (gl,  , root (bV',  , s),  , root (bV1,  , nil),  , eqn1))(* (case label of
               Body =>
                 let
                  val _ = print "abstractEVarNFap -- flag true; we have seen X before\n"
                   val BV = I.BVar(apos + depth)
                   val BV' = I.BVar(i + depth)
                   val BV1 = I.BVar(apos + depth)
                   val (posEA', Vars', S, eqn1) = abstractSub (flag, Gs, (epos, apos - 1), Vars, Gl, total, depth, s, I.Nil, eqn)
                 in
                   (posEA', Vars', I.Root(BV, I.Nil), TableParam.Unify(Gl, I.Root(BV', S), I.Root(BV1, I.Nil ), eqn1))
                 end
              | TyeLabel =>
                 let
                   val Vars' = update (eqEVar X) Vars
                   val (posEA', Vars'', S, eqn1) = abstractSub (flag, Gs, (epos, apos), Vars', Gl, total, depth, s, I.Nil, eqn)
                 in
                   (posEA', Vars'', I.Root(I.BVar(i + depth), S), eqn1)
                 end) *)
 else (* do not enforce linearization -- used for type labels *)
let let  in in (posEA',  , vars',  , root (bVar (i + depth),  , s),  , eqn1) nONE -> (* we have not seen X before *)
if flag then (* enforce linearization since X is not fully applied *)
let let  inlet  inlet  inlet  inlet  in in (posEA',  , vars',  , root (bV,  , nil),  , unify (gl,  , root (bV',  , s),  , root (bV1,  , nil),  , eqn1)) else (* do not enforce linearization -- used for type labels *)
let let  in in (posEA',  , vars',  , root (bVar (epos + depth),  , s),  , eqn1)(* abstractSub (flag, Gs, posEA, Vars, Gl, total, depth, s, S, eqn) = (posEA', Vars', S', eqn')

       (implicit raising)
       (for posEA, Vars, eqn explanation see above)

       let K* = K, Dup

       S' = {{s}}_K* @@ S

       Invariant:
       If    G, Gl |- s : G1
       and  |Gl| = depth

       and   {{Dup}} {{K}} ||- s
       then {{Dup}} {{K}}, G, Gl |- S' : {G1}.W > W   (for some W)
       and  . ||- S'
    *)
 abstractSub(flag,  , gs,  , posEA,  , vars,  , gl,  , total,  , depth,  , shift (k),  , s,  , eqn) if k < depth then abstractSub (flag,  , gs,  , posEA,  , vars,  , gl,  , total,  , depth,  , dot (idx (k + 1),  , shift (k + 1)),  , s,  , eqn) else (* k = depth *)
(posEA,  , vars,  , s,  , eqn) abstractSub(flag,  , gs,  , posEA,  , vars,  , gl,  , total,  , depth,  , dot (idx (k),  , s),  , s,  , eqn) abstractSub (flag,  , gs,  , posEA,  , vars,  , gl,  , total,  , depth,  , s,  , app (root (bVar (k),  , nil),  , s),  , eqn) abstractSub(flag,  , gs,  , posEA,  , vars,  , gl,  , total,  , depth,  , dot (exp (u),  , s),  , s,  , eqn) let let  in in abstractSub (flag,  , gs,  , posEA',  , vars',  , gl,  , total,  , depth,  , s,  , app (u',  , s),  , eqn')(* abstractSpine (flag, Gs, posEA, Vars, Gl, total, depth, (S, s), eqn) = (posEA', Vars', S', eqn')
       where S' = {{S[s]}}_K*   and K* = K, Dup

       Invariant:
       If   Gl, G |- s : G1     G1 |- S : V > P
       and  K* ||- S
       and  |G| = depth

       then {{K*}}, G, G |- S' : V' > P'
       and  . ||- S'
    *)
 abstractSpine(flag,  , gs,  , posEA,  , vars,  , gl,  , total,  , depth,  , (nil,  , _),  , eqn) (posEA,  , vars,  , nil,  , eqn) abstractSpine(flag,  , gs,  , posEA,  , vars,  , gl,  , total,  , depth,  , (sClo (s,  , s'),  , s),  , eqn) abstractSpine (flag,  , gs,  , posEA,  , vars,  , gl,  , total,  , depth,  , (s,  , comp (s',  , s)),  , eqn) abstractSpine(flag,  , gs,  , posEA,  , vars,  , gl,  , total,  , depth,  , (app (u,  , s),  , s),  , eqn) let let  inlet  in in (posEA'',  , vars'',  , app (u',  , s'),  , eqn'')(* abstractSub' (flag, Gs, epos, K, Gl, total, s) = (epos', K', s')      (implicit raising)

        Invariant:
        If   G |- s : G1
       and  |G| = depth
       and  K ||- s
       and {{K}}, G |- {{s}}_K : G1
       then Gs, G |- s' : G1    where  s' == {{s}}_K

         *)
 abstractSub'(flag,  , gs,  , epos,  , vars,  , total,  , shift (k)) if k < 0 then raise (error ("Substitution out of range\n")) else (epos,  , vars,  , shift (k + total)) abstractSub'(flag,  , gs,  , epos,  , vars,  , total,  , dot (idx (k),  , s)) let let  in in (epos',  , vars',  , dot (idx (k),  , s')) abstractSub'(flag,  , gs,  , epos,  , vars,  , total,  , dot (exp (u),  , s)) let let  inlet  in in (epos'',  , vars'',  , dot (exp (u'),  , s'))(* abstractDec (Gs, posEA, Vars, Gl, total, depth, (x:V, s)) = (posEA', Vars', x:V')
       where V = {{V[s]}}_K*

       Invariant:
       If   G |- s : G1     G1 |- V : L
       and  K* ||- V
       and  |G| = depth

       then {{K*}}, G |- V' : L
       and  . ||- V'
    *)
 abstractDec(gs,  , posEA,  , vars,  , gl,  , total,  , depth,  , (dec (x,  , v),  , s),  , nONE) let (*      val (posEA', Vars', V', _) = abstractExp (false, Gs, posEA, Vars, Gl, total, depth, (V, s), TableParam.Trivial)*)
let  in in (posEA',  , vars',  , dec (x,  , v'),  , eqn) abstractDec(gs,  , posEA,  , vars,  , gl,  , total,  , depth,  , (dec (x,  , v),  , s),  , sOME (eqn)) let (*      val (posEA', Vars', V', _) = abstractExp (false, Gs, posEA, Vars, Gl, total, depth, (V, s), TableParam.Trivial)*)
let  in in (posEA',  , vars',  , dec (x,  , v'),  , eqn')(* abstractCtx (Gs, epos, K, total, depth, C.DProg(G,dPool)) = (epos', K', G')
       where G' = {{G}}_K

       Invariants:
       If K ||- G
       and |G| = depth
       then {{K}} |- G' ctx
       and . ||- G'
       and epos = current epos

       note: we will linearize all dynamic assumptions in G.
    *)
let rec abstractCtx'(gs,  , epos,  , vars,  , total,  , depth,  , dProg (null,  , null),  , g',  , eqn) (epos,  , vars,  , g',  , eqn) abstractCtx'(gs,  , epos,  , vars,  , total,  , depth,  , dProg (decl (g,  , d),  , decl (dPool,  , parameter)),  , g',  , eqn) let let  inlet  in in abstractCtx' (gs,  , epos',  , vars',  , total,  , depth - 1,  , dProg (g,  , dPool),  , decl (g',  , d'),  , eqn) abstractCtx'(gs,  , epos,  , vars,  , total,  , depth,  , dProg (decl (g,  , d),  , decl (dPool,  , _)),  , g',  , eqn) let let  inlet  in in abstractCtx' (gs,  , epos',  , vars',  , total,  , depth - 1,  , dProg (g,  , dPool),  , decl (g',  , d'),  , eqn)(*        let
          val d = IntSyn.ctxLength (G)
          val ((epos', _), Vars', D', eqn') = abstractDec (Gs, (epos, total), Vars, I.Null, total , depth - 1, (D, I.id), SOME(eqn))
        in
          abstractCtx' (Gs, epos', Vars', total, depth - 1, C.DProg(G, dPool), I.Decl (G', D'), eqn')
        end
*)
let rec abstractCtx(gs,  , epos,  , vars,  , total,  , depth,  , dProg) abstractCtx' (gs,  , epos,  , vars,  , total,  , depth,  , dProg,  , null,  , trivial)(* makeEVarCtx (Gs, Kall, D, K, eqn) = G'  *)
let rec makeEVarCtx(gs,  , vars,  , dEVars,  , null,  , total) dEVars makeEVarCtx(gs,  , vars,  , dEVars,  , decl (k',  , (_,  , eV (e as eVar (_,  , gX,  , vX,  , _)))),  , total) let let  inlet  inlet  inlet  in in dEVars''let rec makeAVarCtx(vars,  , dupVars) let let rec avarCtx(vars,  , null,  , k) null avarCtx(vars,  , decl (k',  , aV (e as eVar (ref nONE,  , gX,  , vX,  , _),  , d)),  , k) decl (avarCtx (vars,  , k',  , k + 1),  , aDec (sOME ("AVar " ^ toString k ^ "--" ^ toString d),  , d)) avarCtx(vars,  , decl (k',  , aV (e as eVar (_,  , gX,  , vX,  , _),  , d)),  , k) decl (avarCtx (vars,  , k',  , k + 1),  , aDec (sOME ("AVar " ^ toString k ^ "--" ^ toString d),  , d)) in avarCtx (vars,  , dupVars,  , 0)(* add case for foreign expressions ? *)
(* lowerEVar' (G, V[s]) = (X', U), see lowerEVar *)
let rec lowerEVar'(x,  , g,  , (pi ((d',  , _),  , v'),  , s')) let let  inlet  in in (x',  , lam (d'',  , u)) lowerEVar'(x,  , g,  , vs') let let  in in (x',  , x')(* lowerEVar1 (X, V[s]), V[s] in whnf, see lowerEVar *)
 (* lowerEVar1 (X, I.EVar (r, G, _, _), (V as I.Pi _, s)) = *)
lowerEVar1(x,  , eVar (r,  , g,  , _,  , _),  , (v as pi _,  , s)) let let  in in eVar (ref (sOME (u)),  , null,  , v,  , ref nil) lowerEVar1(_,  , x,  , _) x(* lowerEVar (X) = X'

       Invariant:
       If   G |- X : {{G'}} P
            X not subject to any constraints
       then G, G' |- X' : P

       Effect: X is instantiated to [[G']] X' if G' is empty
               otherwise X = X' and no effect occurs.
    *)
 lowerEVar(e,  , x as eVar (r,  , g,  , v,  , ref nil)) lowerEVar1 (e,  , x,  , whnf (v,  , id)) lowerEVar(e,  , eVar _) raise (error "abstraction : LowerEVars: Typing ambiguous -- constraint of functional type cannot be simplified")(* evarsToSub (K, s') = s
      Invariant:
      if K = EV Xn ... EV X2, EV X1
        then
        s = X1 . X2 . ... s'
     *)
let rec evarsToSub(null,  , s) s evarsToSub(decl (k',  , (_,  , eV (e as eVar (i as (ref nONE),  , gX,  , vX,  , cnstr)))),  , s) let let  in(* redundant ? *)
let  inlet  in in dot (exp (x),  , s')(* evarsToSub (K, s') = s
      Invariant:
      if K = AV Xn ... AV X2, EV X1
        then
        s = X1 . X2 . ... s'
     *)
let rec avarsToSub(null,  , s) s avarsToSub(decl (vars',  , (aV (e as eVar (i,  , gX,  , vX,  , cnstr),  , d))),  , s) let let  inlet  in in dot (exp (eClo (x',  , shift (~ d))),  , s')(* abstractEVarCtx (G, p, s) = (G', D', U', s')

     if G |- p[s] and s contains free variables X_n .... X_1
     then
       D' |- Pi  G' . U'
       where D' is the abstraction over the free vars X_n .... X_1

       and s' is a substitution the free variables
            X_n .... X_1, s.t.

       . |- s' : D'

       . |- (Pi G' .U' )[s']  is equivalent to . |- Pi G . p[s]

       Note: G' and U' are possibly strengthened
   *)
let rec abstractEVarCtx(dp as dProg (g,  , dPool),  , p,  , s) let let  inlet  in(* K ||- G i.e. K contains all EVars in G *)
let  in(* DupVars' , K' ||- p[s]  i.e. K' contains all EVars in (p,s) and G and
                                         DupVars' contains all duplicate EVars p[s] *)
let  inlet  inlet  inlet  in(* {{G}}_Vars' , i.e. abstract over the existential variables in G*)
let  in(* abstract over existential variables in p[s] and linearize the expression *)
let  inlet  in(* note: depth will become negative during makeEVarCtx *)
let  inlet  inlet  in in if (! strengthen) then let let  inlet  inlet  in in (gs',  , dAVars,  , dEVars,  , u',  , eqn',  , s'') else (g'',  , dAVars,  , dEVars,  , u',  , eqn',  , s'')let  in(* abstractAnswSub s = (D', s')

   if  |- s : Delta' and s may contain free variables and
     D |- Pi G. U  and  |- s : D and  |- (Pi G . U)[s]
    then

    D' |- s' : D   where D' contains all the
    free variables from s
   *)
let  inlet  inend