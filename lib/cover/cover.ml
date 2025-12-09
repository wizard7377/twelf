(* Coverage Checking *)
(* Author: Frank Pfenning *)

module Cover
  (Global : GLOBAL)
   (Whnf : WHNF)
   (Conv : CONV)
   (*! sharing Whnf.IntSyn = IntSyn' !*)
   (Abstract : ABSTRACT)
   (*! sharing Abstract.IntSyn = IntSyn' !*)
   (Unify : UNIFY)              (* must be trailing! *)
   (*! sharing Unify.IntSyn = IntSyn' !*)
   (Constraints : CONSTRAINTS)
   (*! sharing Constraints.IntSyn = IntSyn' !*)
   (ModeTable : MODETABLE)
   (UniqueTable : MODETABLE)
   (Index : INDEX)
   (*! sharing Index.IntSyn = IntSyn' !*)
   (Subordinate : SUBORDINATE)
   (*! sharing Subordinate.IntSyn = IntSyn' !*)

   (WorldSyn : WORLDSYN)
   (Names : NAMES)
   (*! sharing Names.IntSyn = IntSyn' !*)
   (*! (Paths : PATHS) !*)
   (Print : PRINT)
   (*! sharing Print.IntSyn = IntSyn' !*)
   (TypeCheck : TYPECHECK)
   (*! sharing TypeCheck.IntSyn = IntSyn' !*)
   (*! (CSManager : CS_MANAGER) !*)
   (*! sharing CSManager.IntSyn = IntSyn' !*)
   (Timers : TIMERS)
  : COVER =
struct
  exception Error of string

  local
    module I = IntSyn
    module T = Tomega
    module M = ModeSyn
    module W = WorldSyn
    module P = Paths
    module F = Print.Formatter
    module N = Names


    (*****************)
    (* Strengthening *)
    (*****************)

    (* next section adapted from m2/metasyn.fun *)

    (* weaken (G, a) = w'

       Invariant:
       If   a is a type family
       then G |- w' : G'
       and  forall x:A in G'  A subordinate to a
     *)
    let rec weaken = function (I.Null, a) -> I.id
      | (I.Decl (G', D as I.Dec (name, V)), a) -> 
        let
          let w' = weaken (G', a)
        in
          if Subordinate.belowEq (I.targetFam V, a) then I.dot1 w'
          else I.comp (w', I.shift)
        end
      (* added next case, probably should not arise *)
      (* Sun Dec 16 10:42:05 2001 -fp !!! *)
      (*
      | (I.Decl (G', D as I.BDec _), a) -> 
           I.dot1 (weaken (G', a))
      *)

    (* createEVar (G, V) = X[w] where G |- X[w] : V

       Invariant:
       If G |- V : L
       then G |- X[w] : V
    *)
    let rec createEVar (G, V) =
        let (* G |- V : L *)
          let w = weaken (G, I.targetFam V)       (* G  |- w  : G'    *)
          let iw = Whnf.invert w                  (* G' |- iw : G     *)
          let G' = Whnf.strengthen (iw, G)
          let X' = Whnf.newLoweredEVar (G', (V, iw)) (* G' |- X' : V[iw] *)
          (* was I.newEvar (G', I.EClo (V, iw))  Mon Feb 28 14:30:36 2011 --cs *)
          let X = I.EClo (X', w)                  (* G  |- X  : V     *)
        in
          X
        end

    (*************************)
    (* Coverage instructions *)
    (*************************)

    (* Coverage instructions mirror mode spines, but they
       are computed from modes differently for input and output coverage.

       Match  --- call match and generate candidates
       Skip   --- ignore this argument for purposes of coverage checking

       For input coverage, match input (+) and skip ignore ( * ) and output (-).

       For output coverage, skip input (+), and match output (-).
       Ignore arguments ( * ) should be impossible for output coverage
    *)
    type CoverInst =
        Match of CoverInst
      | Skip of CoverInst
      | Cnil

    (* inCoverInst (ms) = ci
       converts mode spine ms to cover instructions ci for input coverage
    *)
    let rec inCoverInst = function (M.Mnil) -> Cnil
      | (M.Mapp (M.Marg (M.Plus, x), ms')) -> 
          Match (inCoverInst ms')
      | (M.Mapp (M.Marg (M.Minus, x), ms')) -> 
          Skip (inCoverInst ms')
      | (M.Mapp (M.Marg (M.Star, x), ms')) -> 
          Skip (inCoverInst ms')

    (* outCoverInst (ms) = ci
       converts mode spine ms to cover instructions ci for output coverage
    *)
    let rec outCoverInst = function (M.Mnil) -> Cnil
      | (M.Mapp (M.Marg (M.Plus, x), ms')) -> 
          Skip (outCoverInst ms')
      | (M.Mapp (M.Marg (M.Minus, x), ms')) -> 
          Match (outCoverInst ms')
      (* this last case should be impossible *)
      (* output coverage only from totality checking, where there can be *)
      (* no undirectional ( * ) arguments *)
      (*
      | (M.Mapp (M.Marg (M.Star, x), ms')) -> 
          Skip (outCoverInst ms')
      *)

    (***************************)
    (* Printing Coverage Goals *)
    (***************************)

    (* labels for cases for tracing coverage checker *)
    type caseLabel =
        Top                             (* ^ *)
      | Child of caseLabel * int        (* lab.n, n >= 1 *)

    let rec labToString = function (Top) -> "^"
      | (Child(lab, n)) -> labToString(lab) ^ "." ^ Int.toString(n)

    let rec chatter chlev f =
        if !Global.chatter >= chlev
          then print (f ())
        else ()

    let rec pluralize = function (1, s) -> s
      | (n, s) -> s ^ "s"

    (* we pass in the mode spine specifying coverage, but currently ignore it *)
    let rec abbrevCSpine (S, ci) = S

    (* fix to identify existential and universal prefixes *)
    let rec abbrevCGoal = function (G, V, 0, ci) -> (G, abbrevCGoal' (G, V, ci))
      | (G, I.Pi((D, P), V), p, ci) -> (* p > 0 *)
        let
          let D' = N.decEName (G, D)
        in
          abbrevCGoal (I.Decl (G, D'), V, p-1, ci)
        end
    and abbrevCGoal' (G, I.Pi((D, P), V), ci) =
        let
          let D' = N.decUName (G, D)
        in
          I.Pi ((D', P), abbrevCGoal' (I.Decl (G, D'), V, ci))
        end
      | abbrevCGoal' (G, I.Root (a, S), ci) =
          I.Root (a, abbrevCSpine (S, ci))
      (* other cases are impossible by CGoal invariant *)

    let rec formatCGoal (V, p, ci) =
        let
          let _ = N.varReset I.Null
          let (G, V') = abbrevCGoal (I.Null, V, p, ci)
        in
          F.HVbox [Print.formatCtx (I.Null, G), F.Break, F.String "|-",
                   F.Space, Print.formatExp (G, V')]
        end

    let rec formatCGoals = function ((V,p)::nil, ci) -> [formatCGoal (V, p, ci)]
      | ((V,p)::Vs, ci) -> 
          formatCGoal (V, p, ci) :: F.String "," :: F.Break :: formatCGoals (Vs, ci)

    let rec missingToString (Vs, ci) =
        F.makestring_fmt (F.Hbox [F.Vbox0 0 1 (formatCGoals (Vs, ci)), F.String "."])

    let rec showSplitVar (V, p, k, ci) =
        let
          let _ = N.varReset I.Null
          let (G, V') = abbrevCGoal (I.Null, V, p, ci)
          let I.Dec (SOME(x), _) = I.ctxLookup (G, k)
        in
          "Split " ^ x ^ " in " ^ Print.expToString (G, V')
        end

    let rec showPendingGoal (V, p, ci, lab) =
          F.makestring_fmt (F.Hbox [F.String(labToString(lab)), F.Space, F.String "?- ",
                                    formatCGoal (V, p, ci), F.String "."])

    (*
       Coverage goals have the form {{G}} {{L}} a @ S
       where G are splittable variables
       and L are local parameters (not splittable)
    *)
    (**********************************************)
    (* Creating the initial input coverage goal ***)
    (**********************************************)

    (* buildSpine n = n; n-1; ...; 1; Nil *)

    let rec buildSpine = function 0 -> I.Nil
      | n -> (* n > 0 *)
        (* Eta-long invariant violation -kw *)
        I.App (I.Root (I.BVar(n), I.Nil), buildSpine (n-1))

    (* initCGoal' (a, 0, ., V) = ({x1:V1}...{xn:Vn} a x1...xn, n)
       for |- a : V and V = {x1:V1}...{xn:Vn} type

       Invariants for initCGoal' (a, k, G, V):
       G = {x1:V1}...{xk:Vk}
       V = {xk+1:Vk+1}...{xn:Vn} type
       G |- V : type
    *)
    let rec initCGoal' = function (a, k, G, I.Pi ((D, P), V)) -> 
        let
          let D' = N.decEName (G, D)
          let (V', p) = initCGoal' (a, k+1, I.Decl(G, D'), V)
        in
          (I.Pi ((D', I.Maybe), V'), p)
        end
      | (a, k, G, I.Uni (I.Type)) -> 
          (I.Root (a, buildSpine k), k)

    (* initCGoal (a) = {x1:V1}...{xn:Vn} a x1...xn
       where a : {x1:V1}...{xn:Vn} type
    *)
    let rec initCGoal (a) = initCGoal' (I.Const (a), 0, I.Null, I.constType (a))

    (****************)
    (*** Matching ***)
    (****************)

    type CoverClauses =
        Input of I.Exp list
      | Output of I.Exp * int (* for now, no factoring --- singleton list *)

    (* Equation G |- (U1,s1) = (U2,s2)
       Invariant:
       G |- U1[s1] : V
       G |- U2[s2] : V  for some V

       U1[s1] has no EVars (part of coverage goal)
    *)
    type Equation = Eqn of I.dctx * I.eclo * I.eclo

    let rec equationToString (Eqn (G, Us1, Us2)) =
        let let G' = Names.ctxLUName G
          let fmt =
              F.HVbox [Print.formatCtx (I.Null, G'), F.Break,
                       F.String "|-", F.Space,
                       Print.formatExp (G', I.EClo (Us1)), F.Break,
                       F.String "=", F.Space,
                       Print.formatExp (G', I.EClo (Us2))]
        in
          F.makestring_fmt (fmt)
        end

    let rec eqnsToString = function (nil) -> ".\n"
      | (eqn::eqns) -> 
          equationToString (eqn) ^ ",\n"
          ^ eqnsToString (eqns)

    (* Splitting candidates *)
    (* Splitting candidates [k1,...,kl] are indices
       into coverage goal {xn:Vn}...{x1:V1} a M1...Mm, counting right-to-left
    *)
    type Candidates =
        Eqns of Equation list           (* equations to be solved, everything matches so far *)
      | Cands of int list               (* candidates for splitting, matching fails *)
      | Fail                            (* coverage fails without candidates *)

    let rec candsToString = function (Fail) -> "Fail"
      | (Cands(ks)) -> "Cands [" ^ List.foldl (fn (k,str) => Int.toString k ^ "," ^ str) "]" ks
      | (Eqns(eqns)) -> "Eqns [\n" ^ eqnsToString eqns ^ "]"

    (* fail () = Fail
       indicate failure without splitting candidates
     *)
    let rec fail (msg) =
        (chatter 7 (fn () => msg ^ "\n");
         Fail)

    (* failAdd (k, cands) = cands'
       indicate failure, but add k as splitting candidate
    *)
    let rec failAdd = function (k, Eqns _) -> Cands (k::nil) (* no longer matches *)
      | (k, Cands (ks)) -> Cands (k::ks) (* remove duplicates? *)
      | (k, Fail) -> Fail

    (* addEqn (e, cands) = cands'
       indicate possible match if equation e can be solved
    *)
    let rec addEqn = function (e, Eqns (es)) -> Eqns (e::es) (* still may match: add equation *)
      | (e, cands as Cands (ks)) -> (* already failed: ignore new constraints *)
          cands
      | (e, Fail) -> Fail         (* already failed without candidates *)

    let rec unifiable (G, Us1, Us2) =
          Unify.unifiable (G, Us1, Us2)

    (* matchEqns (es) = true
       iff  all equations in es can be simultaneously unified

       Effect: instantiate EVars right-hand sides of equations.
    *)
    let rec matchEqns = function (nil) -> true
      | (Eqn (G, Us1, Us2 as (U2, s2))::es) -> 
        (* For some reason, s2 is sometimes not a patSub when it should be *)
        (* explicitly convert if possible *)
        (* Sat Dec  7 20:59:46 2002 -fp *)
        (* was: unifiable (G, Us1, Us2) *)
        (case Whnf.makePatSub s2
           of NONE => unifiable (G, Us1, Us2) (* constraints will be left in this case *)
            | SOME(s2') => unifiable (G, Us1, (U2, s2')))
        andalso matchEqns (es)

    (* resolveCands (cands) = cands'
       resolve to one of
         Eqns(nil) - match successful
         Fail      - no match, no candidates
         Cands(ks) - candidates ks
       Effect: instantiate EVars in right-hand sides of equations.
    *)
    let rec resolveCands = function (Eqns (es)) -> 
        (* reversed equations Fri Dec 28 09:39:55 2001 -fp !!! *)
        (* why is this important? --cs !!! *)
        if matchEqns (List.rev es) then (Eqns (nil))
        else Fail
      | (Cands (ks)) -> Cands (ks)
      | (Fail) -> Fail

    (* collectConstraints (Xs) = constrs
       collect all the constraints that may be attached to EVars Xs

       try simplifying away the constraints in case they are "hard"
       disabled for now to get a truer approximation to operational semantics
    *)
    let rec collectConstraints = function (nil) -> nil
      | (I.EVar (_, _, _, ref nil)::Xs) -> 
          collectConstraints Xs
      | (I.EVar (_, _, _, ref constrs)::Xs) -> 
          (* constrs <> nil *)
          (* Constraints.simplify constrs @ *) (* at present, do not simplify -fp *)
          constrs @ collectConstraints Xs

    (* checkConstraints (cands, (Q, s)) = cands'
       failure if constraints remain in Q[s] which indicates only partial match
       Q[s] is the clause head after matching the coverage goal.

       Invariants: if cands = Eqns (es) then es = nil.
    *)
    (* This ignores LVars, because collectEVars does *)
    (* Why is that OK?  Sun Dec 16 09:01:40 2001 -fp !!! *)
    let rec checkConstraints = function (G, Qs, Cands (ks)) -> Cands (ks)
      | (G, Qs, Fail) -> Fail
      | (G, Qs, Eqns _) -> (* _ = nil *)
        let
          let Xs = Abstract.collectEVars (G, Qs, nil)
          let constrs = collectConstraints Xs
        in
          case constrs
            of nil => Eqns (nil)
             | _ => Fail                (* constraints remained: Fail without candidates *)
        end

    (* Candidate Lists *)
    (*
       Candidate lists record constructors and candidates for each
       constructors or indicate that the coverage goal is matched.
    *)
    type CandList =
        Covered                         (* covered---no candidates *)
      | CandList of Candidates list     (* cands1,..., candsn *)

    (* addKs (cands, klist) = klist'
       add new constructor to candidate list
    *)
    let rec addKs = function (ccs as Cands(ks), CandList (klist)) -> CandList (ccs::klist)
      | (ces as Eqns(nil), CandList (klist)) -> Covered
      | (cfl as Fail, CandList (klist)) -> CandList (cfl::klist)

    (* matchExp (G, d, (U1, s1), (U2, s2), cands) = cands'
       matches U1[s1] (part of coverage goal)
       against U2[s2] (part of clause head)
       adds new candidates to cands to return cands'
         this could collapse to Fail,
         postponed equations Eqns(es),
         or candidates Cands(ks)
       d is depth, k <= d means local variable, k > d means coverage variable

       Invariants:
       G |- U1[s1] : V
       G |- U2[s2] : V  for some V
       G = Gc, Gl where d = |Gl|
    *)
    let rec matchExp (G, d, Us1, Us2, cands) =
          matchExpW (G, d, Whnf.whnf Us1, Whnf.whnf Us2, cands)

    and matchExpW (G, d, Us1 as (I.Root (H1, S1), s1), Us2 as (I.Root (H2, S2), s2), cands) =
        (case (H1, H2)
           (* Note: I.Proj occurring here will always have the form
              I.Proj (I.Bidx (k), i) *)
           (* No skolem constants, foreign constants, FVars *)
           of (I.BVar (k1), I.BVar(k2)) =>
              if (k1 = k2)
                then matchSpine (G, d, (S1, s1), (S2, s2), cands)
              else if k1 > d
                     then failAdd (k1-d, cands) (* k1 is coverage variable, new candidate *)
                   else fail ("local variable / variable clash") (* otherwise fail with no candidates *)
            | (I.Const(c1), I.Const(c2)) =>
              if (c1 = c2) then matchSpine (G, d, (S1, s1), (S2, s2), cands)
              else fail ("constant / constant clash") (* fail with no candidates *)
            | (I.Def (d1), I.Def (d2)) =>
              if (d1 = d2)              (* because of strictness *)
                then matchSpine (G, d, (S1, s1), (S2, s2), cands)
              else matchExpW (G, d, Whnf.expandDef Us1, Whnf.expandDef Us2, cands)
            | (I.Def (d1), _) => matchExpW (G, d, Whnf.expandDef Us1, Us2, cands)
            | (_, I.Def (d2)) => matchExpW (G, d, Us1, Whnf.expandDef Us2, cands)
            | (I.BVar (k1), I.Const _) =>
              if k1 > d
                then failAdd (k1-d, cands) (* k1 is coverage variable, new candidate *)
              else fail ("local variable / constant clash") (* otherwise fail with no candidates *)
            | (I.Const _, I.BVar _) =>
                fail ("constant / local variable clash")
            | (I.Proj (I.Bidx(k1), i1), I.Proj(I.Bidx(k2), i2)) =>
              if k1 = k2 andalso i1 = i2
                then matchSpine (G, d, (S1, s1), (S2, s2), cands)
              else fail ("block index / block index clash")
            | (I.Proj (I.Bidx(k1), i1), I.Proj(I.LVar(r2, I.Shift(k2), (l2, t2)), i2)) =>
              let
                let I.BDec (bOpt, (l1, t1)) = I.ctxDec (G, k1)
              in
                if l1 <> l2 orelse i1 <> i2
                  then fail ("block index / block variable clash")
                else let let cands2 = matchSub (G, d, t1, I.comp(t2,I.Shift(k2)), cands)
                         (* was: t2 in prev line, July 22, 2010 -fp -cs *)
                         (* instantiate instead of postponing because LVars are *)
                         (* only instantiated to Bidx which are rigid *)
                         (* Sun Jan  5 12:03:13 2003 -fp *)
                         let _ = Unify.instantiateLVar (r2, I.Bidx (k1-k2))
                     in
                       matchSpine (G, d, (S1, s1), (S2, s2), cands2)
                     end
              end
            (* handled in above two cases now *)
            (*
            | (I.Proj (b1, i1), I.Proj (b2, i2)) =>
               if (i1 = i2) then
                 matchSpine (G, d, (S1, s1), (S2, s2),
                             matchBlock (G, d, b1, b2, cands))
               else fail ("block projection / block projection clash")
            *)
            | (I.BVar (k1), I.Proj _) =>
              if k1 > d
                then failAdd (k1-d, cands) (* k1 is splittable, new candidate *)
              else fail ("local variable / block projection clash") (* otherwise fail with no candidates *)
            | (I.Const _, I.Proj _) => fail ("constant / block projection clash")
            | (I.Proj _, I.Const _) => fail ("block projection / constant clash")
            | (I.Proj _, I.BVar _) => fail ("block projection / local variable clash")
            (* no other cases should be possible *)
            )
      | matchExpW (G, d, (I.Lam (D1, U1), s1), (I.Lam (D2, U2), s2), cands) =
           matchExp (I.Decl (G, I.decSub (D1, s1)), d+1, (U1, I.dot1 s1), (U2, I.dot1 s2), cands)
      | matchExpW (G, d, (I.Lam (D1, U1), s1), (U2, s2), cands) =
           (* eta-expand *)
           matchExp (I.Decl (G, I.decSub (D1, s1)), d+1,
                     (U1, I.dot1 s1),
                     (I.Redex (I.EClo (U2, I.shift),
                               I.App (I.Root (I.BVar (1), I.Nil), I.Nil)),
                      I.dot1 s2),
                     cands)
      | matchExpW (G, d, (U1, s1), (I.Lam (D2, U2), s2), cands) =
           (* eta-expand *)
           matchExp (I.Decl (G, I.decSub (D2, s2)), d+1,
                     (I.Redex (I.EClo (U1, I.shift),
                               I.App (I.Root (I.BVar (1), I.Nil), I.Nil)),
                      I.dot1 s1),
                     (U2, I.dot1 s2),
                     cands)
      | matchExpW (G, d, Us1, Us2 as (I.EVar _, s2), cands) =
           addEqn (Eqn (G, Us1, Us2), cands)
      (* next 3 cases are only for output coverage *)
      (* not needed since we skip input arguments for output coverage *)
      (* see comments on CoverInst -fp Fri Dec 21 20:58:55 2001 !!! *)
      (*
      | matchExpW (G, d, (I.Pi ((D1, _), V1), s1), (I.Pi ((D2, _), V2), s2), cands) =
        let
          let cands' = matchDec (G, d, (D1, s1), (D2, s2), cands)
        in
          matchExp (I.Decl (G, D1), d+1, (V1, I.dot1 s1), (V2, I.dot1 s2), cands')
        end
      | matchExpW (G, d, (I.Pi _, _), _, cands) = fail ()
      | matchExpW (G, d, _, (I.Pi _, _), cands) = fail ()
      *)
      (* nothing else should be possible, by invariants *)
      (* No I.Uni, I.FgnExp, and no I.Redex by whnf *)

    and matchSpine (G, d, (I.Nil, _), (I.Nil, _), cands) = cands
      | matchSpine (G, d, (I.SClo (S1, s1'), s1), Ss2, cands) =
          matchSpine (G, d, (S1, I.comp (s1', s1)), Ss2, cands)
      | matchSpine (G, d, Ss1, (I.SClo (S2, s2'), s2), cands) =
          matchSpine (G, d, Ss1, (S2, I.comp (s2', s2)), cands)
      | matchSpine (G, d, (I.App (U1, S1), s1), (I.App (U2, S2), s2), cands) =
        let
          let cands' = matchExp (G, d, (U1, s1), (U2, s2), cands)
        in
          matchSpine (G, d, (S1, s1), (S2, s2), cands')
        end

    and matchDec (G, d, (I.Dec (_, V1), s1), (I.Dec (_, V2), s2), cands) =
          matchExp (G, d, (V1, s1), (V2, s2), cands)
        (* BDec should be impossible here *)

    (* matchBlock now unfolded into the first case of matchExpW *)
    (* Sun Jan  5 12:02:49 2003 -fp *)
    (*
    and matchBlock (G, d, I.Bidx(k), I.Bidx(k'), cands) =
        if (k = k') then cands
          else fail ("block index / block index clash")
      | matchBlock (G, d, B1 as I.Bidx(k), I.LVar (r2, I.Shift(k'), (l2, t2)), cands) =
        (* Updated LVar --cs Sun Dec  1 06:24:41 2002 *)
        let
          let I.BDec (bOpt, (l1, t1)) = I.ctxDec (G, k)
        in
          if l1 <> l2 then fail ("block index / block label clash")
          (* else if k < k' then raise Bind *)
          (* k >= k' by invariant  Sat Dec  7 22:00:41 2002 -fp *)
          else let
                 let cands2 = matchSub (G, d, t1, t2, cands)
                 (* instantiate if matching is successful *)
                 (* let _ = print (candsToString (cands2) ^ "\n") *)
                 (* instantiate, instead of postponing because *)
                 (* LVars are only instantiated to Bidx's which are rigid *)
                 (* !!!BUG!!! r2 and B1 make sense in different contexts *)
                 (* fixed by k-k' Sat Dec  7 21:12:57 2002 -fp *)
                 let _ = Unify.instantiateLVar (r2, I.Bidx (k-k'))
               in
                 cands2
               end
        end
    *)

    and matchSub (G, d, I.Shift(n1), I.Shift(n2), cands) = cands
        (* by invariant *)
      | matchSub (G, d, I.Shift(n), s2 as I.Dot _, cands) =
          matchSub (G, d, I.Dot(I.Idx(n+1), I.Shift(n+1)), s2, cands)
      | matchSub (G, d, s1 as I.Dot _, I.Shift(m), cands) =
          matchSub (G, d, s1, I.Dot(I.Idx(m+1), I.Shift(m+1)), cands)
      | matchSub (G, d, I.Dot(Ft1,s1), I.Dot(Ft2,s2), cands) =
        let let cands1 =
           (case (Ft1, Ft2) of
             (I.Idx (n1), I.Idx (n2)) =>
               if n1 = n2
                 then cands
               else if n1 > d
                      then failAdd (n1-d, cands)
                    else fail ("local variable / local variable clash in block instance")
           | (I.Exp (U1), I.Exp (U2)) =>
                 matchExp (G, d, (U1, I.id), (U2, I.id), cands)
           | (I.Exp (U1), I.Idx (n2)) =>
                 matchExp (G, d, (U1, I.id), (I.Root (I.BVar (n2), I.Nil), I.id), cands)
           | (I.Idx (n1), I.Exp (U2)) =>
                 matchExp (G, d, (I.Root (I.BVar (n1), I.Nil), I.id), (U2, I.id), cands))
        in
          matchSub (G, d, s1, s2, cands1)
        end

    (* matchTop (G, (a @ S1, s1), (a @ S2, s2), ci) = cands
       matches S1[s1] (spine of coverage goal)
       against S2[s2] (spine of clause head)
       skipping over `skip' arguments in cover instructions

       Invariants:
       G |- a @ S1[s1] : type
       G |- a @ S2[s2] : type
       G contains coverage variables,
       S1[s1] contains no EVars
       cover instructions ci matche S1 and S2
    *)
    let rec matchTop (G, d, Us1, Us2, ci, cands) =
          matchTopW (G, d, Whnf.whnf Us1, Whnf.whnf Us2, ci, cands)
    and matchTopW (G, d, (I.Root (I.Const (c1), S1), s1),
                         (I.Root (I.Const (c2), S2), s2), ci, cands) =
        if (c1 = c2)
          then
            (* unify spines, skipping output and ignore arguments in modeSpine *)
            matchTopSpine (G, d, (S1, s1), (S2, s2), ci, cands)
        else fail ("type family clash") (* fails, with no candidates since type families don't match *)
      | matchTopW (G, d, (I.Pi ((D1,_), V1), s1),
                         (I.Pi ((D2,_), V2), s2), ci, cands) =
        (* this case can only arise in output coverage *)
        (* we do not match D1 and D2, since D1 is always an instance of D2 *)
        (* and no splittable variables should be suggested here *)
        (* Sat Dec 22 23:53:44 2001 -fp !!! *)
          matchTopW (I.Decl (G, D1), d+1, (V1, I.dot1 s1), (V2, I.dot1 s2), ci, cands)
    and matchTopSpine (G, d, (I.Nil, _), (I.Nil, _), Cnil, cands) = cands
      | matchTopSpine (G, d, (I.SClo (S1, s1'), s1), Ss2, ci, cands) =
          matchTopSpine (G, d, (S1, I.comp (s1', s1)), Ss2, ci, cands)
      | matchTopSpine (G, d, Ss1, (I.SClo (S2, s2'), s2), ci, cands) =
          matchTopSpine (G, d, Ss1, (S2, I.comp (s2', s2)), ci, cands)
      | matchTopSpine (G, d, (I.App (U1, S1), s1), (I.App (U2, S2), s2),
                       Match (ci'), cands) =
        (* an argument that must be covered (Match) *)
        let
          let cands' = matchExp (G, d, (U1, s1), (U2, s2), cands)
        in
           matchTopSpine (G, d, (S1, s1), (S2, s2), ci', cands')
        end
      | matchTopSpine (G, d, (I.App (U1, S1), s1), (I.App (U2, S2), s2),
                       Skip (ci'), cands) =
        (* an argument that need not be covered (Skip) *)
           matchTopSpine (G, d, (S1, s1), (S2, s2), ci', cands)

    (* matchClause (G, (a @ S1, s1), V, ci) = cands
       as in matchTop, but r is clause
       NOTE: Simply use constant type for more robustness (see below)
    *)
    let rec matchClause = function (G, ps', qs as (I.Root (_, _), s), ci) -> 
          checkConstraints (G, qs, resolveCands (matchTop (G, 0, ps', qs, ci, Eqns (nil))))
      | (G, ps', (I.Pi ((I.Dec(_, V1), _), V2), s), ci) -> 
        let
          (* changed to use subordination and strengthening here *)
          (* Sun Dec 16 10:39:34 2001 -fp *)
          (* let X1 = createEVar (G, I.EClo (V1, s)) *)
          (* changed back --- no effect *)
          let X1 = Whnf.newLoweredEVar (G, (V1, s))
          (* was let X1 = I.newEVar (G, I.EClo (V1, s)) Mon Feb 28 14:37:22 2011 -cs *)
          (* was: I.Null instead of G in line above Wed Nov 21 16:40:40 2001 *)
        in
          matchClause (G, ps', (V2, I.Dot (I.Exp (X1), s)), ci)
        end

    (* matchSig (G, (a @ S, s), ccs, ci, klist) = klist'
       match coverage goal {{G}} a @ S[s]
       against each coverage clause V in ccs,
       adding one new list cand for each V to klist to obtain klist'

       Invariants:
       G |- a @ S[s] : type
       V consists of clauses with target type a @ S'
       ci matches S
       klist <> Covered
    *)
    let rec matchSig = function (G, ps', nil, ci, klist) -> klist
      | (G, ps', V::ccs', ci, klist) -> 
        let
          let cands = CSManager.trail
                      (fn () => matchClause (G, ps', (V, I.id), ci))
        in
          matchSig' (G, ps', ccs', ci, addKs (cands, klist))
        end

    (* matchSig' (G, (a @ S, s), ccs, ci, klist) = klist'
       as matchSig, but check if coverage goal {{G}} a @ S[s] is already matched
    *)
    and matchSig' (G, ps', ccs, ci, Covered) = Covered (* already covered: return *)
      | matchSig' (G, ps', ccs, ci, CandList (klist)) = (* not yet covered: continue to search *)
          matchSig (G, ps', ccs, ci, CandList (klist))

    (* matchBlocks (G, s', piDecs, V, k, i, ci, klist) = klist'
       Invariants:
       G |- s' : Gsome
       Gsome |- piDecs : ctx
       G |- V : type
       G_k = (Gsome, D1...D(i-1) piDecs)
     *)
    let rec matchBlocks = function (G, s', nil, V, k, i, ci, klist) -> klist
      | (G, s', I.Dec (_, V')::piDecs, V, k, i, ci, klist) -> 
        let
          let cands = CSManager.trail
                      (fn () => matchClause (G, (V, I.id), (V', s'), ci))
          let s'' = I.Dot (I.Exp (I.Root (I.Proj (I.Bidx k, i), I.Nil)), s')
        in
          matchBlocks' (G, s'', piDecs, V, k, i+1, ci, addKs (cands, klist))
        end
    and matchBlocks' (G, s', piDecs, V, k, i, ci, Covered) = Covered
      | matchBlocks' (G, s', piDecs, V, k, i, ci, klist) =
          matchBlocks (G, s', piDecs, V, k, i, ci, klist) (* klist <> Covered *)

    (* matchCtx (G, s', G', V, k, ci, klist) = klist'
       Invariants:
       G |- s' : G'
       G |- V : type
       s' o ^ = ^k
       ci matches for for V = a @ S
       klist <> Covered accumulates mode spines
    *)
    let rec matchCtx = function (G, s', I.Null, V, k, ci, klist) -> klist
      | (G, s', I.Decl(G'', I.Dec(_, V')), V, k, ci, klist) -> 
        (* will always fail for input coverage *)
        let
          (*  G'', V' |- ^ : G''
              G |- s' : G'', V'
          *)
          let s'' = I.comp (I.shift, s')
          (*  G |- ^ o s' : G'' *)
          let cands = CSManager.trail
                      (fn () => matchClause (G, (V, I.id), (V', s''), ci))
        in
          matchCtx' (G, s'', G'', V, k+1, ci, addKs (cands, klist))
        end
      | (G, s', I.Decl(G'', I.BDec(_, (cid, s))), V, k, ci, klist) -> 
        let
          let (Gsome, piDecs) = I.constBlock cid
          let s'' = I.comp (I.shift, s')
          (* G'' |- s : Gsome,
             G |- s'' : G''
             G |- s o s'' : Gsome
             Gsome |- piDecs : ctx
          *)
          let klist' = matchBlocks (G, I.comp (s, s''), piDecs, V, k, 1, ci, klist)
        in
          matchCtx' (G, s'', G'', V, k+1, ci, klist')
        end

    and matchCtx' (G, s', G', V, k, ci, Covered) = Covered
      | matchCtx' (G, s', G', V, k, ci, CandList (klist)) =
          matchCtx (G, s', G', V, k, ci, CandList (klist))

    (* as matchClause *)
    let rec matchOut = function (G, V, ci, (V', s'), 0) -> 
        let
          let cands = matchTop (G, 0, (V, I.id), (V', s'), ci, Eqns(nil))
          let cands' = resolveCands (cands)
          let cands'' = checkConstraints (G, (V', s'), cands')
        in
          addKs (cands'', CandList (nil))
        end
      | (G, V, ci, (V' as I.Pi ((I.Dec(_, V1'), _), V2'), s'), p) -> (* p > 0 *)
        let
          let X1 = Whnf.newLoweredEVar (G, (V1', s'))
        (* was let X1 = I.newEVar (G, I.EClo (V1', s')) Mon Feb 28 14:38:21 2011 -cs *)
        in
          matchOut (G, V, ci, (V2', I.Dot (I.Exp (X1), s')), p-1)
        end

    (* match (., V, p, ci, I/O(ccs)) = klist
       matching coverage goal {{G}} V against coverage clauses Vi in ccs
       yields candidates klist
       no local assumptions
       Invariants:
       V = {{G}} {{L}} a @ S where |G| = p
       cover instructions ci match S
       G |- V : type
    *)
    let rec match = function (G, V as I.Root (I.Const (a), S), 0, ci, Input(ccs)) -> 
          matchCtx' (G, I.id, G, V, 1, ci,
                     matchSig (G, (V, I.id), ccs, ci, CandList (nil)))
      | (G, V, 0, ci, Output (V', q)) -> 
          matchOut (G, V, ci, (V', I.Shift (I.ctxLength G)), q)
      | (G, I.Pi ((D, _), V'), p, ci, ccs) -> 
          match (I.Decl (G, D), V', p-1, ci, ccs)

    (************************************)
    (*** Selecting Splitting Variable ***)
    (************************************)

    (* insert (k, ksn) = ksn'
       ksn is ordered list of ks (smallest index first) with multiplicities
    *)
    let rec insert = function (k, nil) -> ((k, 1)::nil)
      | (k, ksn as (k', n')::ksn') -> 
        (case Int.compare (k, k')
           of LESS => (k, 1)::ksn
            | EQUAL => (k', n'+1)::ksn'
            | GREATER => (k', n')::insert (k, ksn'))

    (* join (ks, ksn) = ksn'
       ksn is as in function insert
    *)
    let rec join = function (nil, ksn) -> ksn
      | (k::ks, ksn) -> join (ks, insert (k, ksn))

    (* selectCand (klist) = ksnOpt
       where ksOpt is an indication of coverage (NONE)
       or a list of candidates with multiplicities

       Simple heuristic: select last splitting candidate from last clause tried
       This will never pick an index variable unless necessary.
    *)
    let rec selectCand = function (Covered) -> NONE     (* success: case is covered! *)
      | (CandList (klist)) -> selectCand' (klist, nil)

    and selectCand' (nil, ksn) = SOME(ksn) (* failure: case G,V is not covered! *)
      | selectCand' (Fail::klist, ksn) = (* local failure (clash) and no candidates *)
          selectCand' (klist, ksn)
      | selectCand' (Cands(nil)::klist, ksn) = (* local failure but no candidates *)
          selectCand' (klist, ksn)
      | selectCand' (Cands(ks)::klist, ksn) = (* found candidates ks <> nil *)
          selectCand' (klist, join (ks, ksn))

    (*****************)
    (*** Splitting ***)
    (*****************)

    (* In a coverage goal {{G}} {{L}} a @ S we instantiate each
       declaration in G with a new EVar, then split one of these variables,
       then abstract to obtain a new coverage goal {{G'}} {{L'}} a @ S'
    *)

    (* instEVars ({x1:V1}...{xp:Vp} V, p, nil) = (V[s], [X1,...,Xn])
       where . |- s : {x1:V1}...{xp:Vp}
       and s = Xp...X1.id, all Xi are new EVars
    *)
    let rec instEVars (Vs, p, XsRev) = instEVarsW (Whnf.whnf Vs, p, XsRev)
    and instEVarsW (Vs, 0, XsRev) = (Vs, XsRev)
      | instEVarsW ((I.Pi ((I.Dec (xOpt, V1), _), V2), s), p, XsRev) =
        let (* p > 0 *)
          let X1 = Whnf.newLoweredEVar (I.Null, (V1, s)) (* all EVars are global *)
          (* was  let X1 = I.newEVar (I.Null, I.EClo (V1, s)) (* all EVars are global *)
             Mon Feb 28 14:39:15 2011 -cs *)
        in
          instEVars ((V2, I.Dot (I.Exp (X1), s)), p-1, SOME(X1)::XsRev)
        end
      | instEVarsW ((I.Pi ((I.BDec (_, (l, t)), _), V2), s), p, XsRev) =
        (* G0 |- t : Gsome *)
        (* . |- s : G0 *)
        let (* p > 0 *)
          let L1 = I.newLVar (I.Shift(0), (l, I.comp(t, s)))
          (* new -fp Sun Dec  1 20:58:06 2002 *)
          (* new -cs  Sun Dec  1 06:27:57 2002 *)
        in
          instEVars ((V2, I.Dot (I.Block (L1), s)), p-1, NONE::XsRev)
        end

    (* caseList is a list of possibilities for a variables
       to be split.  Maintained as a mutable reference so it
       can be updated in the success continuation.
    *)
    local
      let caseList : (I.Exp * int) list ref = ref nil
    in
      let rec resetCases () = (caseList := nil)
      let rec addCase (V, p) = (caseList := (V,p) :: !caseList)
      let rec getCases () = (!caseList)
    end

    (* createEVarSpine (G, (V, s)) = (S', (V', s'))

       Invariant:
       If   G |- s : G1   and  G1 |- V = Pi {V1 .. Vn}. W : L
       and  G1, V1 .. Vn |- W atomic
       then G |- s' : G2  and  G2 |- V' : L
       and  S = X1; ...; Xn; Nil
       and  G |- W [1.2...n. s o ^n] = V' [sjfh']
       and  G |- S : V [s] >  V' [s']
    *)
    (* changed to use createEVar? *)
    (* Sun Dec 16 10:36:59 2001 -fp *)
    let rec createEVarSpine (G, Vs) = createEVarSpineW (G, Whnf.whnf Vs)
    and createEVarSpineW (G, Vs as (I.Root _, s)) = (I.Nil, Vs)   (* s = id *)
      | createEVarSpineW (G, (I.Pi ((D as I.Dec (_, V1), _), V2), s)) =
        let (* G |- V1[s] : L *)
          let X = createEVar (G, I.EClo (V1, s))
          let (S, Vs) = createEVarSpine (G, (V2, I.Dot (I.Exp (X), s)))
        in
          (I.App (X, S), Vs)
        end
      (* Uni or other cases should be impossible *)

    (* createAtomConst (G, c) = (U', (V', s'))

       Invariant:
       If   S |- c : Pi {V1 .. Vn}. V
       then . |- U' = c @ (X1; .. Xn; Nil)
       and  . |- U' : V' [s']
    *)
    let rec createAtomConst (G, H as I.Const (cid)) =
        let
          let V = I.constType cid
          let (S, Vs) = createEVarSpine (G, (V, I.id))
        in
          (I.Root (H, S), Vs)
        end
        (* mod: m2/metasyn.fun allows skolem constants *)

    (* createAtomBVar (G, k) = (U', (V', s'))

       Invariant:
       If   G |- k : Pi {V1 .. Vn}. V
       then . |- U' = k @ (Xn; .. Xn; Nil)
       and  . |- U' : V' [s']
    *)
    let rec createAtomBVar (G, k) =
        let
          let I.Dec (_, V) = I.ctxDec (G, k)
          let (S, Vs) = createEVarSpine (G, (V, I.id))
        in
          (I.Root (I.BVar (k), S), Vs)
        end

    (* end m2/metasyn.fun *)

    (* createAtomProj (G, #i(l), (V, s)) = (U', (V', s'))

       Invariant:
       If   G |- #i(l) : Pi {V1 .. Vn}. Va
       and  G |- Pi {V1..Vn}. Va = V[s] : type
       then . |- U' = #i(l) @ (X1; .. Xn; Nil)
       and  . |- U' : V' [s']
    *)
    let rec createAtomProj (G, H, (V, s)) =
        let
          let (S, Vs') = createEVarSpine (G, (V, s))
        in
          (I.Root (H, S), Vs')
        end

    let rec constCases = function (G, Vs, nil, sc) -> ()
      | (G, Vs, I.Const(c)::sgn', sc) -> 
        let
          let (U, Vs') = createAtomConst (G, I.Const c)
          let _ = CSManager.trail (fn () =>
                                   if Unify.unifiable (G, Vs, Vs')
                                     then sc U
                                   else ())
        in
          constCases (G, Vs, sgn', sc)
        end

    let rec paramCases = function (G, Vs, 0, sc) -> ()
      | (G, Vs, k, sc) -> 
        let
          let (U, Vs') = createAtomBVar (G, k)
          let _ = CSManager.trail (fn () =>
                                   if Unify.unifiable (G, Vs, Vs')
                                     then sc U
                                   else ())
        in
          paramCases (G, Vs, k-1, sc)
        end

    (* createEVarSub G' = s

       Invariant:
       If   . |- G' ctx
       then . |- s : G' and s instantiates each x:A with an EVar . |- X : A

       Update: Always use empty context. Sat Dec  8 13:19:58 2001 -fp
    *)
    let rec createEVarSub = function (I.Null) -> I.id
      | (I.Decl(G', D as I.Dec (_, V))) -> 
        let
          let s = createEVarSub G'
          let X = Whnf.newLoweredEVar (I.Null, (V, s))
          (* was   let V' = I.EClo (V, s)
                   let X = I.newEVar (I.Null, V') Mon Feb 28 15:32:09 2011 --cs *)
        in
          I.Dot (I.Exp X, s)
        end

    (* hack *)
    let rec blockName (cid) = I.conDecName (I.sgnLookup (cid))

    (* blockCases (G, Vs, B, (Gsome, piDecs), sc) =

       If G |- V[s] : type
          . |- Gsome ctx and Gsome |- piDecs decList
       then sc is called for any x:A in piDecs such thtat
            G |- V[s] = A[t] : type
            where t instantiates variable in Gsome with new EVars
    *)
    let rec blockCases (G, Vs, cid, (Gsome, piDecs), sc) =
        let
          let t = createEVarSub Gsome
          (* . |- t : Gsome *)
          let sk = I.Shift (I.ctxLength(G))
          let t' = I.comp (t, sk)
          (* was: the above, using t' for t below *)
          let lvar = I.newLVar (sk, (cid, t))
                     (*  BUG. Breach in the invariant:
                         G |- sk : .
                         . |- t: Gsome
                         G <> .

                         replace t by t' in I.newLVar (sk, (cid, t))
                      --cs Fri Jan  3 11:07:41 2003 *)
          (* G |- t' : Gsome *)
        in
          blockCases' (G, Vs, (lvar, 1), (t', piDecs), sc)
        end
    and blockCases' (G, Vs, (lvar, i), (t, nil), sc) = ()
      | blockCases' (G, Vs, (lvar, i), (t, I.Dec (_, V')::piDecs), sc) =
        let
          (* G |- t : G' and G' |- ({_:V'},piDecs) decList *)
          (* so G |- V'[t'] : type *)
          let (U, Vs') = createAtomProj (G, I.Proj (lvar, i), (V', t))
          let _ = CSManager.trail (fn () => if Unify.unifiable (G, Vs, Vs')
                                              then sc U
                                            else ())
          let t' = I.Dot (I.Exp (I.Root (I.Proj (lvar, i), I.Nil)), t)
        in
          blockCases' (G, Vs, (lvar, i+1), (t', piDecs), sc)
        end

    let rec worldCases = function (G, Vs, T.Worlds (nil), sc) -> ()
      | (G, Vs, T.Worlds (cid::cids), sc) -> 
          ( blockCases (G, Vs, cid, I.constBlock cid, sc) ;
            worldCases (G, Vs, T.Worlds (cids), sc) )

    let rec lowerSplitW = function (X as I.EVar (_, G, V, _), W, sc) -> 
        let
          let sc' = fun U ->  if Unify.unifiable (G, (X, I.id), (U, I.id))
                                then sc ()
                              else ()
          let _ = paramCases (G, (V, I.id), I.ctxLength G, sc') (* will trail *)
          let _ = worldCases (G, (V, I.id), W, sc') (* will trail *)
          let _ = constCases (G, (V, I.id), Index.lookup (I.targetFam V), sc') (* will trail *)
        in
          ()
        end
      | (I.Lam (D, U), W, sc) -> 
          lowerSplitW (U, W, sc)

    (* splitEVar (X, W, sc) = ()

       calls sc () for all cases, after instantiation of X
       W are the currently possible worlds
    *)
    let rec splitEVar (X, W, sc) = lowerSplitW (X, W, sc)

(* was
   let rec lowerSplit (G, Vs, W, sc, print) = lowerSplitW (G, Whnf.whnf Vs, W, sc, print)
    and lowerSplitW (G, Vs as (I.Root (I.Const a, _), s), W, sc, pr) =
        let
(*        let _ = print ("Consider P cases for "  ^ Print.expToString (G, I.EClo Vs) ^ "\n")
let _ = pr () *)
          let _ = paramCases (G, Vs, I.ctxLength G, sc) (* will trail *)
(*        let _ = print ("Consider W cases for "  ^ Print.expToString (G, I.EClo Vs) ^ "\n")
let _ = pr () *)
          let _ = worldCases (G, Vs, W, sc) (* will trail *)
(*        let _ = print ("Consider C cases for "  ^ Print.expToString (G, I.EClo Vs) ^ "\n") *)
          let _ = constCases (G, Vs, Index.lookup a, sc) (* will trail *)
        in
          ()
        end
      | lowerSplitW (G, (I.Pi ((D, P), V), s), W, sc, print) =
        let
          let D' = I.decSub (D, s)
        in
          lowerSplit (I.Decl (G, D'), (V, I.dot1 s), W, fun U -> sc (I.Lam (D', U)), print)
        end

   let rec splitEVar ((X as I.EVar (_, GX, V, _)), W, sc, print) = (* GX = I.Null *)
         lowerSplit (I.Null, (V, I.id), W,
                      fun U -> if Unify.unifiable (I.Null, (X, I.id), (U, I.id))
                                then sc ()
                              else (), print)
    Mon Feb 28 14:49:04 2011 -cs *)

    (* abstract (V, s) = V'
       where V' = {{G}} Vs' and G abstracts over all EVars in V[s]
       in arbitrary order respecting dependency

       Invariants: . |- V[s] : type
       Effect: may raise Constraints.Error (constrs)
     *)
    let rec abstract (V, s) =
        let
          let (i, V') = Abstract.abstractDecImp (I.EClo (V, s))
          let _ = if !Global.doubleCheck
                    then TypeCheck.typeCheck (I.Null, (V', I.Uni(I.Type)))
                  else ()
        in
          (V', i)
        end

    (* splitVar ({{G}} V, p, k, W) = SOME [{{G1}} V1 ,..., {{Gn}} Vn]
                                  or NONE
       where {{Gi}} Vi are new coverage goals obtained by
       splitting kth variable in G, counting right-to-left.

       returns NONE if splitting variable k fails because of constraints

       W are the worlds defined for current predicate

       Invariants:
       |G| = p
       k <= |G|
       G |- V : type
       {{Gi}} Vi cover {{G}} V
    *)
    let rec splitVar (V, p, k, (W, ci)) =
        let
          let _ = chatter 6 (fn () => showSplitVar (V, p, k, ci) ^ "\n")
          let ((V1, s), XsRev) = instEVars ((V, I.id), p, nil)
          (* split on k'th variable, counting from innermost *)
          let SOME(X) = List.nth (XsRev, k-1)
          let _ = resetCases ()
          let _ = splitEVar (X, W, fn () => addCase (abstract (V1, s))) (* may raise Constraints.Error *)
        in
          SOME (getCases ())
        end
        (* Constraints.Error could be raised by abstract *)
        handle Constraints.Error (constrs) =>
          (chatter 7 (fn () => "Inactive split:\n" ^ Print.cnstrsToString (constrs) ^ "\n");
           NONE)

    (**********************)
    (* Finitary Splitting *)
    (**********************)

    (*
       A splittable variable X : V is called finitary
       if there are finitely many alternatives for V.
       This means there are finitely many (including 0)
       constructors (possibly including local variables) such that
       all free variables in the argument are not recursive
       with the target type of V.

       Splitting such variables can never lead to non-termination.
    *)

    (* Stolen from abstract.fun *)

    let rec occursInExp = function (k, I.Uni _) -> false
      | (k, I.Pi (DP, V)) -> occursInDecP (k, DP) orelse occursInExp (k+1, V)
      | (k, I.Root (H, S)) -> occursInHead (k, H) orelse occursInSpine (k, S)
      | (k, I.Lam (D, V)) -> occursInDec (k, D) orelse occursInExp (k+1, V)
      | (k, I.FgnExp (cs, ops)) -> false
        (* foreign expression probably should not occur *)
        (* but if they do, variable occurrences don't count *)
        (* occursInExp (k, Whnf.normalize (#toInternal(ops) (), I.id)) *)
      (* no case for Redex, EVar, EClo *)

    and occursInHead (k, I.BVar (k')) = (k = k')
      | occursInHead (k, _) = false

    and occursInSpine (_, I.Nil) = false
      | occursInSpine (k, I.App (U, S)) = occursInExp (k, U) orelse occursInSpine (k, S)
      (* no case for SClo *)

    and occursInDec (k, I.Dec (_, V)) = occursInExp (k, V)
    and occursInDecP (k, (D, _)) = occursInDec (k, D)

    (* occursInMatchPos (k, U, ci) = true
       if k occur in U in a matchable position according to the coverage
       instructions ci
    *)
    let rec occursInMatchPos = function (k, I.Pi (DP, V), ci) -> 
          occursInMatchPos (k+1, V, ci)
      | (k, I.Root (H, S), ci) -> 
          occursInMatchPosSpine (k, S, ci)
    and occursInMatchPosSpine (k, I.Nil, Cnil) = false
      | occursInMatchPosSpine (k, I.App(U, S), Match(ci)) =
          occursInExp (k, U) orelse occursInMatchPosSpine (k, S, ci)
      | occursInMatchPosSpine (k, I.App(U, S), Skip(ci)) =
          occursInMatchPosSpine (k, S, ci)

    (* instEVarsSkip ({x1:V1}...{xp:Vp} V, p, nil, ci) = (V[s], [X1,...,Xn])
       where . |- s : {x1:V1}...{xp:Vp}
       and s = Xp...X1.id, all Xi are new EVars that actually occur in a "Match" argument
       and ci are the coverage instructions (Match or Skip) for the target type of V
    *)
    let rec instEVarsSkip (Vs, p, XsRev, ci) = InstEVarsSkipW (Whnf.whnf Vs, p, XsRev, ci)
    and InstEVarsSkipW (Vs, 0, XsRev, ci) = (Vs, XsRev)
      | InstEVarsSkipW ((I.Pi ((I.Dec (xOpt, V1), _), V2), s), p, XsRev, ci) =
        let (* p > 0 *)
          let X1 = Whnf.newLoweredEVar (I.Null, (V1, s)) (* all EVars are global *)
          (* was let X1 = I.newEVar (I.Null, I.EClo (V1, s)) (* all EVars are global *)
             Mon Feb 28 15:25:42 2011 --cs *)
          let EVarOpt = if occursInMatchPos (1, V2, ci)
                          then SOME(X1)
                        else NONE
        in
          instEVarsSkip ((V2, I.Dot (I.Exp (X1), s)), p-1, EVarOpt::XsRev, ci)
        end
      | InstEVarsSkipW ((I.Pi ((I.BDec (_, (l, t)), _), V2), s), p, XsRev, ci) =
        (* G0 |- t : Gsome *)
        (* . |- s : G0 *)
        let (* p > 0 *)
          let L1 = I.newLVar (I.Shift(0), (l, I.comp(t, s)))
          (* -fp Sun Dec  1 21:09:38 2002 *)
          (* -cs Sun Dec  1 06:30:59 2002 *)
        in
          instEVarsSkip ((V2, I.Dot (I.Block (L1), s)), p-1, NONE::XsRev, ci)
        end

    let rec targetBelowEq = function (a, I.EVar (ref(NONE), GY, VY, ref nil)) -> 
          Subordinate.belowEq (a, I.targetFam VY)
      | (a, I.EVar (ref(NONE), GY, VY, ref (_::_))) -> 
          (* if contraints remain, consider recursive and thereby unsplittable *)
          true

    (* recursive X = true
       iff the instantiation of X : {{G}} a @ S contains an
           EVar Y : {{G'}} b @ S such that a <|= b

       This means there is no guarantee that X : {{G}} a @ S has only
       a finite number of instances
    *)
    let rec recursive = function (X as I.EVar (ref(SOME(U)), GX, VX, _)) -> 
        let (* GX = I.Null*)
            (* is this always true? --cs!!!*)
          let a = I.targetFam VX
          let Ys = Abstract.collectEVars (GX, (X, I.id), nil)
          (* LVars are ignored here.  OK because never splittable? *)
          (* Sat Dec 15 22:42:10 2001 -fp !!! *)
          let recp = List.exists (fun Y -> targetBelowEq (a, Y)) Ys
        in
          recp
        end
      | (I.Lam (D, U)) -> recursive U

    local
      let counter = ref 0
    in
      let rec resetCount () = (counter := 0)
      let rec incCount () = (counter := !counter + 1)
      let rec getCount () = !counter
    end

    exception NotFinitary

    (* finitary1 (X, k, W, f, cands)
        = ((k, n)::cands) if X is finitary with n possibilities
        = cands if X is not finitary
    *)
    (* The function f has been added to ensure that k is splittable without
       constraints.   In the previous version, this check was not performed.
       nat : type.
       z : nat.
       s : nat -> nat.

       eqz :  nat -> type.
       eqz_z : eqz z.

       unit : type.
       * : unit.

       test : {f : unit -> nat} eqz (f * ) -> type.
       %worlds () (test _ _).
       %covers test +F +Q.  %% loops!
        Counterexample due to Andrzej.  Fix due to Adam.
        Mon Oct 15 15:08:25 2007 --cs
    *)
    let rec finitary1 (X, k, W, f, cands) =
        ( resetCount () ;
          chatter 7 (fn () => "Trying " ^ Print.expToString (I.Null, X) ^ " : "
                     ^ ".\n") ;
          ( splitEVar (X, W, fn () => (f (); if recursive X
                                        then raise NotFinitary
                                      else incCount ())) ;
            chatter 7 (fn () => "Finitary with " ^ Int.toString (getCount ()) ^ " candidates.\n");

            (k, getCount ())::cands )
           handle NotFinitary => ( chatter 7 (fn () => "Not finitary.\n");
                                   cands )
                 | Constraints.Error (constrs) =>
                                 ( chatter 7 (fn () => "Inactive finitary split.\n");
                                   cands )
        )

    (* was Mon Feb 28 15:29:36 2011 -cs
    let rec finitary1 (X as I.EVar(r, I.Null, VX, _), k, W, f, cands, print) =
        ( resetCount () ;
          chatter 7 (fn () => "Trying " ^ Print.expToString (I.Null, X) ^ " : "
                     ^ Print.expToString (I.Null, VX) ^ ".\n") ;
          ( splitEVar (X, W, fn () => (f (); if recursive X
                                        then raise NotFinitary
                                      else incCount ()), print) ;
            chatter 7 (fn () => "Finitary with " ^ Int.toString (getCount ()) ^ " candidates.\n");

            (k, getCount ())::cands )
           handle NotFinitary => ( chatter 7 (fn () => "Not finitary.\n");
                                   cands )
                 | Constraints.Error (constrs) =>
                                 ( chatter 7 (fn () => "Inactive finitary split.\n");
                                   cands )
        )
    *)


    (* finitarySplits (XsRev, k, W, cands) = [(k1,n1),...,(km,nm)]@cands
       where all ki are finitary with ni possibilities for X(i+k)
    *)
    let rec finitarySplits = function (nil, k, W, f, cands) -> cands
      | (NONE::Xs, k, W, f, cands) -> 
        (* parameter blocks can never be split *)
          finitarySplits (Xs, k+1, W, f, cands)
      | (SOME(X)::Xs, k, W, f, cands) -> 
          finitarySplits (Xs, k+1, W, f, CSManager.trail (fn () =>  finitary1 (X, k, W, f,cands)))

    (* finitary ({{G}} V, p, W) = [(k1,n1),...,(km,nm)]
       where ki are indices of splittable variables in G with ni possibilities
       and |G| = p
       and ci are the coverage instructions for the target type of V
    *)

    let rec finitary (V, p, W, ci) =
        let
          let _ = if !Global.doubleCheck
                    then TypeCheck.typeCheck (I.Null, (V, I.Uni (I.Type)))
                  else ()

          let ((V1, s), XsRev) = instEVarsSkip ((V, I.id), p, nil, ci)
        in
          finitarySplits (XsRev, 1, W, fn () => (abstract (V1, s)), nil)
        end


    (***********************************)
    (* Contraction based on uniqueness *)
    (***********************************)

    (* eqExp (U[s], U'[s']) = true iff G |- U[s] == U'[s'] : V
       Invariants:
         G |- U[s] : V
         G |- U'[s'] : V
         U[s], U'[s'] contain no EVars
       Note that the typing invariant is satisfied because
       input arguments can only depend on other input arguments,
       but not undetermined or output arguments.
       Similar remarks apply to functions below
    *)
    let rec eqExp (Us, Us') = Conv.conv (Us, Us')

    (* eqInpSpine (ms, S1[s1], S2[s2]) = true
       iff U1[s1] == U2[s2] for all input (+) arguments in S1, S2
       according to uniqueness mode spine ms
       Invariants: typing as in eqExp, ms ~ S1, ms ~ S2
    *)
    let rec eqInpSpine = function (ms, (I.SClo(S1,s1'),s1), Ss2) -> 
          eqInpSpine (ms, (S1, I.comp(s1',s1)), Ss2)
      | (ms, Ss1, (I.SClo(S2,s2'),s2)) -> 
          eqInpSpine (ms, Ss1, (S2, I.comp(s2',s2)))
      | (M.Mnil, (I.Nil,s), (I.Nil,s')) -> true
      | eqInpSpine (M.Mapp(M.Marg(M.Plus,_), ms'),
                  (I.App(U,S),s), (I.App(U',S'),s')) =
          eqExp ((U,s), (U',s'))
          andalso eqInpSpine (ms', (S,s), (S',s'))
      | (M.Mapp(_, ms'), (I.App(U,S),s), (I.App(U',S'),s')) -> 
          (* ignore Star, Minus, Minus1 *)
          eqInpSpine (ms', (S,s), (S',s'))
      (* other cases should be impossible since spines must match *)

    (* eqInp (G, k, a, S[s], ms) = [k1+k,...,kn+k]
       where k1,...,kn are the deBruijn indices of those declarations
       ki:a @ Si in such that G0 |- Si[^ki+k] == S[s] on all input arguments
       according to mode spine ms.
       Here G = ...kn:a @ Sn, ..., k1:a @ S1, ...
    *)
    let rec eqInp = function (I.Null, k, a, Ss, ms) -> nil
      | (I.Decl(G', I.Dec(_, I.Root (I.Const(a'), S'))), k, a, Ss, ms) -> 
        (* defined type families disallowed here *)
        if a = a' andalso eqInpSpine (ms, (S', I.Shift(k)), Ss)
          then k::eqInp (G', k+1, a, Ss, ms)
        else eqInp (G', k+1, a, Ss, ms)
      | (I.Decl(G', I.Dec(_, I.Pi _)), k, a, Ss, ms) -> 
          eqInp (G', k+1, a, Ss, ms)
      | (I.Decl(G', I.NDec _), k, a, Ss, ms) -> 
          eqInp (G', k+1, a, Ss, ms)
      | (I.Decl(G', I.BDec(_, (b, t))), k, a, Ss, ms) -> 
          eqInp (G', k+1, a, Ss, ms)
      (* other cases should be impossible *)

    (* contractionCands (G, k) = [[k11,...,k1{n1}],...,[km1,...,km{nm}]]
       where each [kj1,...,kj{nj}] are deBruijn indices in G (counting from right)
       such that kji:aj @ Sji ... kj{nj}:aj @ Sj{nj} and
       Sji...Sj{nj} agree on their input arguments according to the
       uniqueness mode spine for aj
    *)
    let rec contractionCands = function (I.Null, k) -> nil
      | (I.Decl(G', I.Dec(_, I.Root (I.Const(a), S))), k) -> 
        (* defined type families disallowed here *)
        (* using only one uniqueness declaration per type family *)
        (case UniqueTable.modeLookup a
           of NONE => contractionCands (G', k+1)
            | SOME(ms) =>
              case eqInp (G', k+1, a, (S, I.Shift(k)), ms)
                of nil => contractionCands (G', k+1)
                 | ns => (k::ns)::contractionCands (G', k+1))
      | (I.Decl(G', I.Dec(_, I.Pi _)), k) -> 
          (* ignore Pi --- contraction cands unclear *)
          contractionCands (G', k+1)
      | (I.Decl(G', I.NDec _), k) -> 
          contractionCands (G', k+1)
      | (I.Decl(G', I.BDec(_, (b, t))), k) -> 
          (* ignore blocks --- contraction cands unclear *)
          contractionCands (G', k+1)

    (* isolateSplittable ((G0, {{G1}}V, p) = ((G0@G1), V) where |G1| = p
       This isolates the splittable variable G1@G1 from an old-style
       coverage goal ({{G}}V, p)
    *)
    let rec isolateSplittable = function (G, V, 0) -> (G, V)
      | (G, I.Pi((D,_), V'), p) -> 
          isolateSplittable (I.Decl(G, D), V', p-1)

    (* unifyUOutSpine (ms, S1[s1], S2[s2]) = true
       iff U1[s1] == U2[s2] for all unique output (-1) arguments in S1, S2
       according to uniqueness mode spine ms
       Invariants: the input arguments in S1[s1] and S2[s2] must be known
          to be equal, ms ~ S1, ms ~ S2
       Effect: EVars in S1[s1], S2[s2] are instantianted, both upon
          failure and success
    *)
    let rec unifyUOutSpine = function (ms, (I.SClo(S1,s1'),s1), Ss2) -> 
          unifyUOutSpine (ms, (S1, I.comp(s1', s1)), Ss2)
      | (ms, Ss1, (I.SClo(S2,s2'),s2)) -> 
          unifyUOutSpine (ms, Ss1, (S2, I.comp(s2',s2)))
      | (M.Mnil, (I.Nil,s1), (I.Nil,s2)) -> true
      | (M.Mapp(M.Marg(M.Minus1,_),ms'), (I.App(U1,S1),s1), (I.App(U2,S2),s2)) -> 
          Unify.unifiable (I.Null, (U1,s1), (U2,s2)) (* will have effect! *)
          andalso unifyUOutSpine (ms', (S1,s1), (S2,s2))
      | (M.Mapp(_,ms'), (I.App(U1,S1),s1), (I.App(U2,S2), s2)) -> 
          (* if mode = + already equal by invariant; otherwise ignore *)
          unifyUOutSpine (ms', (S1,s1), (S2,s2))
      (* Nil/App or App/Nil cannot occur by invariants *)

    (* unifyUOuttype (a @ S1, a @ S2) = true
       iff S1 and S2 unify on all unique output (-1) arguments in S1, S2
       according to uniqueness mode declaration for a (both args must have same a)
       Invariants: the input args in S1, S2 must be known to be equal
          and a must have a uniqueness mode
       Effect: Evars may be instantiated by unification
    *)
    let rec unifyUOutType (V1, V2) =
          unifyUOutTypeW (Whnf.whnf (V1, I.id), Whnf.whnf(V2, I.id))
    and unifyUOutTypeW ((I.Root(I.Const(a1),S1),s1), (I.Root(I.Const(a2),S2),s2)) =
        (* a1 = a2 by invariant *)
        let
          let SOME(ms) = UniqueTable.modeLookup a1 (* must succeed by invariant *)
        in
          unifyUOutSpine (ms, (S1,s1), (S2,s2))
        end
        (* must be constant-headed roots by invariant *)

    (* unifyUOutEvars (X1, X2) = true
       iff . |- X1 : a @ S1, . |- X2 : a @ S2 and the unique output arguments
       in V1 and V2 unify
       Invariants: the input args in S1, S2, must be known to be equal
         Both types start with the same a, a must have a uniqueness mode
       Effect: Evars may be instantiated by unification
    *)
    let rec unifyUOutEVars (SOME(I.EVar(_, G1, V1, _)), SOME(I.EVar(_, G2, V2, _))) =
          (* G1 = G2 = Null *)
          unifyUOutType (V1, V2)

    (* unifyUOut2 ([X1,...,Xp], k1, k2) = (see unifyOutEvars (X{k1}, X{k2})) *)
    let rec unifyUOut2 (XsRev, k1, k2) =
          unifyUOutEVars (List.nth (XsRev, k1-1), List.nth (XsRev, k2-1))

    (* unifyOut1 ([X1,...,Xp], [k1, k2, ..., kn] = true
       if X{k1} "==" X{k2} "==" ... "==" X{kn} according to unifyOutEvars
    *)
    let rec unifyUOut1 = function (XsRev, nil) -> true
      | (XsRev, k1::nil) -> true
      | (XsRev, k1::k2::ks) -> 
          unifyUOut2 (XsRev, k1, k2)
          andalso unifyUOut1 (XsRev, k2::ks)

    (* unifyOut ([X1,...,Xp], [[k11,...,k1{n1}],...,[km1,...,km{nm}]]) = true
       if unifyOut1 ([X1,...,Xp], [kj1,...,kj{nj}]) for each j
    *)
    let rec unifyUOut = function (XsRev, nil) -> true
      | (XsRev, ks::kss) -> 
          unifyUOut1 (XsRev, ks)
          andalso unifyUOut (XsRev, kss)

    (* contractAll ({{G}}V, p, ucands) = SOME(V',p')
       iff (V',p') is the result of contracting unique output arguments
           according to contraction candidates ucands
           of variables in G where all input arguments agree
       returns NONE if unique output arguments are non-unifiable
       may be the identity if output arguments are already identity
          or unsolvable constraints during contraction
       Invariants: p = |G| (G contains the splittable variables)
    *)
    let rec contractAll (V, p, ucands) =
        let
          let ((V1, s), XsRev) = instEVars ((V, I.id), p, nil) (* as in splitVar *)
        in
          if unifyUOut (XsRev, ucands)
            then SOME (abstract (V1, s)) (* as in splitVar, may raise Constraints.Error *)
          else NONE                     (* unique outputs not simultaneously unifiable *)
        end

    (* contract ({{G}}V0, p, ci, lab) = SOME(V',p')
       iff (V',p') is the result of contracting unique output arguments
           of variables in G where all input arguments agree
       returns NONE if unique output arguments are non-unifiable
       may be the identity if output arguments are already identity
          or unsolvable constraints during contraction
       ci and lab are used for printing
       Invariants: p = |G| (G contains the splittable variables)
    *)
    let rec contract (V, p, ci, lab) =
        let
          let (G, _) = isolateSplittable (I.Null, V, p) (* ignore body of coverage goal *)
          let ucands = contractionCands (G, 1)
          let n = List.length ucands
          let _ = if n > 0
                    then chatter 6 (fn () => "Found " ^ Int.toString n ^ " contraction "
                                    ^ pluralize (n, "candidate") ^ "\n")
                  else ()
          let VpOpt' = if n > 0
                         then (contractAll (V, p, ucands)
                               handle Constraints.Error _ =>
                                      ( chatter 6 (fn () => "Contraction failed due to constraints\n");
                                        SOME(V, p) ))
                                        (* no progress if constraints remain *)
                       else SOME(V, p)  (* no candidates, no progress *)
          let _ = case VpOpt'
                    of NONE => chatter 6 (fn () => "Case impossible: conflicting unique outputs\n")
                     | SOME(V',p') => chatter 6 (fn () => showPendingGoal (V', p', ci, lab) ^ "\n")
        in
          VpOpt'
        end

    (*********************)
    (* Coverage Checking *)
    (*********************)

    (* findMin ((k1,n1),...,(km,nm)) = (ki,ni)
       where ni is the minimum among the n1,...,nm
       Invariant: m >= 1
    *)
    let rec findMin ((k,n)::kns) = findMin'((k,n), kns)
    and findMin' ((k0,n0), nil) = (k0,n0)
      | findMin' ((k0,n0), (k',n')::kns) =
        if n' < n0
          then findMin' ((k',n'), kns)
        else findMin' ((k0,n0), kns)

    (* need to improve tracing with higher chatter levels *)
    (* ccs = covering clauses *)

    (* cover (V, p, (W, ci), ccs, lab, missing) = missing'
       covers ([(V1,p1),...,(Vi,pi)], (W, ci), ccs, missing) = missing'

       check if Match arguments (+ for input, - for output) in V or all Vi, respectively,
       are covered by clauses ccs, adding omitted cases to missing to yield missing'.

       V = {{G}} {{L}} a @ S where |G| = p and G contains the splittable
       variables while L contains the local parameters

       W are the worlds for type family a
       ci are the cover instructions matching S

       lab is the label for the current goal for tracing purposes
    *)
    let rec cover (V, p, wci as (W, ci), ccs, lab, missing) =
        ( chatter 6 (fn () => showPendingGoal (V, p, ci, lab) ^ "\n");
          cover' (contract(V, p, ci, lab), wci, ccs, lab, missing) )

    and cover' (SOME(V, p), wci as (W, ci), ccs, lab, missing) =
          split (V, p, selectCand (match (I.Null, V, p, ci, ccs)), wci, ccs, lab, missing)
      | cover' (NONE, wci, ccs, lab, missing) =
        (* V is covered by unique output inconsistency *)
        ( chatter 6 (fn () => "Covered\n");
          missing )

    and split (V, p, NONE, wci, ccs, lab, missing) =
        (* V is covered: return missing patterns from other cases *)
        ( chatter 6 (fn () => "Covered\n");
          missing )
      | split (V, p, SOME(nil), wci as (W, ci), ccs, lab, missing) =
        (* no strong candidates: check for finitary splitting candidates *)
        ( chatter 6 (fn () => "No strong candidates---calculating weak candidates\n");
          splitWeak (V, p, finitary (V, p, W, ci), wci, ccs, lab, missing) )
      | split (V, p, SOME((k,_)::ksn), wci as (W, ci), ccs, lab, missing) =
        (* some candidates: split first candidate, ignoring multiplicities *)
        (* candidates are in reverse order, so non-index candidates are split first *)
        (* splitVar shows splitting as it happens *)
        (case splitVar (V, p, k, wci)
           of SOME(cases) => covers (cases, wci, ccs, lab, missing)
            | NONE => (* splitting variable k generated constraints *)
              split (V, p, SOME (ksn), wci, ccs, lab, missing)) (* try other candidates *)

    and splitWeak (V, p, nil, wci, ccs, lab, missing) =
        ( chatter 6 (fn () => "No weak candidates---case " ^ labToString(lab) ^ " not covered\n");
          (V,p)::missing )
      | splitWeak (V, p, ksn, wci, ccs, lab, missing) = (* ksn <> nil *)
        (* commit to the minimal candidate, since no constraints can arise *)
          split (V, p, SOME(findMin ksn::nil), wci, ccs, lab, missing)

    and covers (cases, wci, ccs, lab, missing) =
        ( chatter 6 (fn () => "Found " ^ Int.toString (List.length cases)
                              ^ pluralize (List.length cases, " case") ^ "\n");
          covers' (cases, 1, wci, ccs, lab, missing) )

    and covers' (nil, n, wci, ccs, lab, missing) =
        ( chatter 6 (fn () => "All subcases of " ^ labToString(lab) ^ " considered\n");
          missing )
      | covers' ((V,p)::cases', n, wci, ccs, lab, missing) =
          covers' (cases', n+1, wci, ccs, lab, cover (V, p, wci, ccs, Child(lab, n), missing))

    (******************)
    (* Input Coverage *)
    (******************)

    (* constsToTypes [c1,...,cn] = [V1,...,Vn] where ci:Vi.
       Generates coverage clauses from module type.
    *)
    let rec constsToTypes = function (nil) -> nil
      | (I.Const(c)::cs') -> I.constType(c)::constsToTypes(cs')
      | (I.Def(d)::cs') -> I.constType(d)::constsToTypes(cs')

    (*******************)
    (* Output Coverage *)
    (*******************)

    (* createCoverClause (G, V, 0) = ({{G}} V, |G|)
       where {{G}} V is in NF
    *)
    let rec createCoverClause = function (I.Decl (G, D), V, p) -> 
          createCoverClause (G, I.Pi ((D, I.Maybe), V), p+1)
      | (I.Null, V, p) -> 
          (Whnf.normalize (V, I.id), p)

    (* createCoverGoal (., ({{G}} {{GL}} a @ S, s), p, ms) = V' with |G| = p
       createCoverGoal (GL, (a @ S, s), 0, ms) = a @ S'
       createCoverSpine ((S, s), (V', s'), ms) = S'

       where all variables in G are replaced by new EVars in V to yield V'
       and output arguments in S are replaced by new EVars in V to yield V'

       G are the externally quantified variables
       GL are the locally introduced parameter for the current subgoal a @ S

       Invariants: . |- ({{G}} {{GL}} a @ S)[s] : type
                   |G| = p
                   ms matches S
                   . | S[s] : V'[s'] > type
                   . |- V'[s'] : type
    *)
    let rec createCoverGoal (G, Vs, p, ms) =
           createCoverGoalW (G, Whnf.whnf (Vs), p, ms)

    and createCoverGoalW (G, (I.Pi ((D1,P1), V2), s), 0, ms) =
        let
          let D1' = I.decSub (D1, s)
          let V2' = createCoverGoal (I.Decl (G, D1'), (V2, I.dot1 s), 0, ms)
        in
          I.Pi ((D1',P1), V2')
        end
      | createCoverGoalW (G, (I.Pi ((D as I.Dec (_, V1), _), V2), s), p, ms) =
        let (* p > 0, G = I.Null *)
          let X = Whnf.newLoweredEVar (G, (V1, s))
          (* was  let X = I.newEVar (G, I.EClo (V1, s))  Mon Feb 28 15:33:52 2011 -cs *)
        in
          createCoverGoal (G, (V2, I.Dot (I.Exp (X), s)), p-1, ms)
        end
      | createCoverGoalW (G, (I.Root (a as I.Const(cid), S), s), p, ms) = (* s = id, p >= 0 *)
        I.Root (a, createCoverSpine (G, (S, s), (I.constType (cid), I.id), ms))

    and createCoverSpine (G, (I.Nil, s), _, M.Mnil) = I.Nil
      | createCoverSpine (G, (I.App (U1, S2), s), (I.Pi ((I.Dec (_, V1), _), V2), s'),
                          M.Mapp (M.Marg (M.Minus, x), ms')) =
        (* replace output argument by new variable *)
        let
          let X = createEVar (G, I.EClo (V1, s')) (* strengthen G based on subordination *)
          let S2' = createCoverSpine (G, (S2, s), (V2, I.Dot (I.Exp (X), s')), ms')
        in
          I.App (X, S2')
        end
      | createCoverSpine (G, (I.App (U1, S2), s), (I.Pi (_, V2), s'), M.Mapp (_, ms')) =
        (* leave input ( + ) arguments as they are, ignore ( * ) impossible *)
          I.App (I.EClo (U1, s),
                 createCoverSpine (G, (S2, s), Whnf.whnf (V2, I.Dot (I.Exp (I.EClo (U1, s)), s')),
                                   ms'))
      | createCoverSpine (G, (I.SClo (S, s'), s), Vs, ms) =
          createCoverSpine (G, (S, I.comp (s', s)), Vs, ms)

  in
    let rec checkNoDef (a) =
        (case I.sgnLookup a
           of I.ConDef _ =>
                raise Error ("Coverage checking " ^ N.qidToString (N.constQid a)
                             ^ ":\ntype family must not be defined.")
            | _ => ())

    (* checkCovers (a, ms) = ()
       checks coverage for type family a with respect to mode spine ms
       Effect: raises Error (msg) otherwise
    *)
    let rec checkCovers (a, ms) =
        let
          let _ = chatter 4 (fn () => "Input coverage checking family " ^ N.qidToString (N.constQid a)
                             ^ "\n")
          let _ = checkNoDef (a)
          let _ = Subordinate.checkNoDef (a)
                  handle Subordinate.Error (msg) =>
                    raise Error ("Coverage checking " ^ N.qidToString (N.constQid a) ^ ":\n"
                                 ^ msg)
          let (V0, p) = initCGoal (a)
          let _ = if !Global.doubleCheck
                    then TypeCheck.typeCheck (I.Null, (V0, I.Uni (I.Type)))
                  else ()
          let _ = CSManager.reset ()
          let cIn = inCoverInst ms      (* convert mode spine to cover instructions *)
          let cs = Index.lookup a       (* lookup constants defining a *)
          let ccs = constsToTypes cs    (* calculate covering clauses *)
          let W = W.lookup a            (* world declarations for a; must be defined *)
          let V0 = createCoverGoal (I.Null, (V0, I.id), p, ms) (* replace output by new EVars *)
          let (V0, p) = abstract (V0, I.id)    (* abstract will double-check *)
          let missing = cover (V0, p, (W, cIn), Input(ccs), Top, nil)
          let _ = case missing
                    of nil => ()        (* all cases covered *)
                     | _::_ => raise Error ("Coverage error --- missing cases:\n"
                                            ^ missingToString (missing, ms) ^ "\n")
        in
          ()
        end

    (* checkOut (G, (V, s)) = ()
       checks if the most general goal V' is locally output-covered by V
       Effect: raises Error (msg) otherwise
    *)
    let rec checkOut (G, (V, s)) =
        let
          let a = I.targetFam V
          let SOME(ms) = ModeTable.modeLookup a (* must be defined and well-moded *)
          let cOut = outCoverInst ms    (* determine cover instructions *)
          let (V', q) = createCoverClause (G, I.EClo(V, s), 0) (* abstract all variables in G *)
          let _ = if !Global.doubleCheck
                    then TypeCheck.typeCheck (I.Null, (V', I.Uni (I.Type)))
                  else ()
          let V0 = createCoverGoal (I.Null, (V', I.id), q, ms) (* replace output by new EVars *)
          let (V0', p) = abstract (V0, I.id)    (* abstract will double-check *)
          let W = W.lookup a
          let missing = cover (V0', p, (W, cOut), Output(V',q), Top, nil)
          let _ = case missing
                    of nil => ()
                     | _::_ => raise Error ("Output coverage error --- missing cases:\n"
                                            ^ missingToString (missing, ms) ^ "\n")
        in
          ()
        end

    (**********************************************)
    (* New code for coverage checking of Tomega   *)
    (* Started Sun Nov 24 11:02:25 2002  -fp      *)
    (* First version Tue Nov 26 19:29:12 2002 -fp *)
    (**********************************************)

    (* cg = CGoal (G, S)  with G |- S : {{G'}} type *)
    type CoverGoal =
      CGoal of I.dctx * I.Spine

    (* cc = CClause (Gi, Si) with  Gi |- Si : {{G}} type *)
    type CoverClause =
      CClause of I.dctx * I.Spine

    let rec formatCGoal (CGoal (G, S)) =
        let
          let _ = N.varReset I.Null
        in
          F.HVbox ([Print.formatCtx (I.Null, G), F.Break, F.Break, F.String "|-",
                    F.Space] @ Print.formatSpine (G, S))
        end

    let rec showPendingCGoal (CGoal (G, S), lab) =
        F.makestring_fmt (F.Hbox [F.String(labToString(lab)), F.Space, F.String "?- ",
                                  formatCGoal (CGoal (G, S)), F.String "."])

    let rec showCClause (CClause (G, S)) =
        let
          let _ = N.varReset I.Null
        in
          F.makestring_fmt (F.HVbox ([F.String "!- "] @ Print.formatSpine (G, S)))
        end

    let rec showSplitVar (CGoal (G, S), k) =
        let
          let _ = N.varReset I.Null
          let I.Dec (SOME(x), _) = I.ctxLookup (G, k)
        in
          "Split " ^ x ^ " in " ^ F.makestring_fmt (F.HVbox (Print.formatSpine (G, S)))
        end

    (* newEVarSubst (G, G') = s
       Invariant:   If G = xn:Vn,...,x1:V1
                  then s = X1...Xn.^k
                     G |- s : G'
    *)
    let rec newEVarSubst = function (G, I.Null) -> I.Shift(I.ctxLength(G))
      | (G, I.Decl(G', D as I.Dec (_, V))) -> 
        let
          let s' = newEVarSubst (G, G')
          let X = Whnf.newLoweredEVar (G, (V, s'))
          (* was let V' = I.EClo (V, s')
                 let X = I.newEVar (G, V') Mon Feb 28 15:34:31 2011 -cs *)
        in
          I.Dot (I.Exp (X), s')
        end
      | (G, I.Decl(G', D as I.NDec _)) -> 
        let
          let s' = newEVarSubst (G, G')
        in
          I.Dot (I.Undef, s')
        end
      | (G, I.Decl(G', D as I.BDec (_, (b, t)))) -> 
        let
          let s' = newEVarSubst (G, G')
          let L1 = I.newLVar (s', (b, t))
          (* was  let L1 = I.newLVar (I.Shift(0), (b, I.comp(t, s')))
             --cs Fri Jul 23 16:39:27 2010 *)

          (* -cs Fri Jul 23 16:35:04 2010  FPCHECK *)
          (* L : Delta[t][G'] *)
          (* G |- s : G'  G |- L[s'] : V[s]
             G |- (L[s'].s : G', V *)
          (* -fp Sun Dec  1 21:10:45 2002 *)
          (* -cs Sun Dec  1 06:31:23 2002 *)
        in
          I.Dot (I.Block (L1), s')
        end
      (* ADec should be impossible *)

    (* checkConstraints (G, Si[ti], cands) = cands'
       failure if constraints remain in Q[s] which indicates only partial match
       Q[s] is the clause head after matching the coverage goal.

       Invariants: if cands = Eqns (es) then es = nil.
    *)
    (* This ignores LVars, because collectEVars does *)
    (* Why is that OK?  Sun Dec 16 09:01:40 2001 -fp !!! *)
    let rec checkConstraints = function (G, (Si, ti), Cands (ks)) -> Cands (ks)
      | (G, (Si, ti), Fail) -> Fail
      | (G, (Si, ti), Eqns _) -> (* _ = nil *)
        let
          let Xs = Abstract.collectEVarsSpine (G, (Si, ti), nil)
          let constrs = collectConstraints Xs
        in
          case constrs
            of nil => Eqns (nil)
             | _ => fail ("Remaining constraints") (* constraints remained: Fail without candidates *)
        end

    (* matchClause (cg, (Si, ti)) = klist
       matching coverage goal cg against instantiated coverage clause Si[ti]
       yields splitting candidates klist
    *)
    let rec matchClause (CGoal (G, S), (Si, ti)) =
        let
          let cands1 = matchSpine (G, 0, (S, I.id), (Si, ti), Eqns (nil))
          let cands2 = resolveCands cands1
          let cands3 = checkConstraints (G, (Si, ti), cands2)
        in
          cands3
        end

    (* matchClauses (cg, ccs, klist) = klist'
       as in match, with accumulator argument klist
    *)
    let rec matchClauses = function (cg, nil, klist) -> klist
      | (cg as CGoal(G, S), (CClause (Gi, Si)::ccs), klist) -> 
        let
          let ti = newEVarSubst (G, Gi) (* G |- ti : Gi *)
          let cands = CSManager.trail (fn () => matchClause (cg, (Si, ti)))
        in
          matchClauses' (cg, ccs, addKs (cands, klist))
        end
    and matchClauses' (cg, ccs, Covered) = Covered
      | matchClauses' (cg, ccs, klist as CandList _) =
          matchClauses (cg, ccs, klist)

    (* match (cg, ccs) = klist
       matching coverage goal cg against coverage clauses ccs
       yields candidates klist
    *)
    let rec match (CGoal (G, S), ccs) =
          matchClauses (CGoal (G, S), ccs, CandList (nil))

    (* abstractSpine (S, s) = CGoal (G, S')
       Invariant: G abstracts all EVars in S[s]
       G |- S' : {{G'}}type
    *)
    let rec abstractSpine (S, s) =
        let
          let (G', S') = Abstract.abstractSpine (S, s)

          let namedG' = N.ctxName G' (* for printing purposes *)
          let _ = if !Global.doubleCheck
                    then ( TypeCheck.typeCheckCtx (namedG')
                          (* TypeCheck.typeCheckSpine (namedG', S') *)
                          )
                  else ()
        in
          CGoal (namedG', S')
        end

    (* kthSub (X1...Xn.^0, k) = Xk
       Invariant: 1 <= k <= n
       Xi are either EVars or to be ignored
    *)
    let rec kthSub = function (I.Dot (I.Exp(X), s), 1) -> X
      | (I.Dot (_, s), k) -> kthSub (s, k-1)

    (* subToXsRev (X1...Xn.^0) = [Xiopt,...,Xnopt]
       Invariant: Xi are either EVars (translate to SOME(Xi))
                  or not (translate to NONE)
    *)
    let rec subToXsRev = function (I.Shift(0)) -> nil (* n = 0 *)
      | (I.Dot (I.Exp(X), s)) -> 
          SOME(X)::subToXsRev (s)
      | (I.Dot (_, s)) -> 
          NONE::subToXsRev (s)

    (* caseList is a list of possibilities for a variables
       to be split.  Maintained as a mutable reference so it
       can be updated in the success continuation.
    *)
    local
      let caseList : CoverGoal list ref = ref nil
    in
      let rec resetCases () = (caseList := nil)
      let rec addCase cg = (caseList := cg :: !caseList)
      let rec getCases () = (!caseList)
    end

    (* splitVar (CGoal(G, S), k, w) = SOME [cg1,...,cgn]
                                  or NONE
       where cgi are new coverage goals obtained by
       splitting kth variable in G, counting right-to-left.

       returns NONE if splitting variable k fails because of constraints

       w are the worlds defined for current predicate

       Invariants:
       k <= |G|
       G |- S : {{G'}} type
       cgi cover cg
    *)
    let rec splitVar (cg as CGoal (G, S), k, w) =
        let
          let _ = chatter 6 (fn () => showSplitVar (cg, k) ^ "\n")
          let s = newEVarSubst (I.Null, G) (* for splitting, EVars are always global *)
          (* G = xn:V1,...,x1:Vn *)
          (* s = X1....Xn.^0, where . |- s : G *)
          let X = kthSub (s, k) (* starts with k = 1 (a la deBruijn) *)
          let _ = resetCases ()
          let _ = splitEVar (X, w, fn () => addCase (abstractSpine (S, s)))
        in
          SOME (getCases ())
        end
        (* Constraints.Error could be raised by abstract *)
        handle Constraints.Error (constrs) =>
          (chatter 7 (fn () => "Inactive split:\n" ^ Print.cnstrsToString (constrs) ^ "\n");
           NONE)

    (* finitary (CGoal (G, S), W) = [(k1,n1),...,(km,nm)]
       where ki are indices of splittable variables in G with ni possibilities
    *)
    let rec finitary (CGoal (G, S), w) =
        let
          (* G = xn:Vn,...,x1:V1 *)
          let s = newEVarSubst (I.Null, G) (* for splitting, EVars are always global *)
          (* s = X1...Xn.^0,  . |- S : G *)
          let XsRev = subToXsRev (s)
          (* XsRev = [SOME(X1),...,SOME(Xn)] *)
        in
          finitarySplits (XsRev, 1, w, fn () => abstractSpine (S, s), nil)
        end

    (***************)
    (* Contraction *)
    (***************)
    (* for explanation, see contract and contractAll above *)

    let rec contractAll (CGoal(G,S), ucands) =
        let
          let s = newEVarSubst (I.Null, G) (* for unif, EVars are always global *)
          let XsRev = subToXsRev (s)
        in
          if unifyUOut (XsRev, ucands)
            then SOME (abstractSpine (S, s)) (* as in splitVar, may raise Constraints.Error *)
          else NONE
        end

    let rec contract (cg as CGoal (G, S), lab) =
        let
          let ucands = contractionCands (G, 1)
          let n = List.length ucands
          let _ = if n > 0
                    then chatter 6 (fn () => "Found " ^ Int.toString n ^ " contraction "
                                    ^ pluralize (n, "candidate") ^ "\n")
                  else ()
          let cgOpt' = if n > 0
                         then (contractAll (cg, ucands)
                               handle Constraints.Error _ =>
                                 ( chatter 6 (fn () => "Contraction failed due to constraints\n");
                                  SOME(cg) )) (* no progress if constraints remain *)
                       else SOME(cg)    (* no candidates, no progress *)
          let _ = case cgOpt'
                    of NONE => chatter 6 (fn () => "Case impossible: conflicting unique outputs\n")
                     | SOME(cg') => chatter 6 (fn () => showPendingCGoal (cg', lab) ^ "\n")
        in
          cgOpt'
        end

    (* cover (cg, w, ccs, lab, missing) = missing'
       covers ([cg1,...,cgn], w, ccs, missing) = missing'

       Check if cover goal cg (or [cg1,..,cgn]) are covered by
       cover clauses ccs, adding missing cases to missing to yield missing'

       cg = CGoal (G, S) where G contains the splittable variables
       cci = CClause (Gi, Si) where Gi contains essentially existential variables

       w are the worlds for the principal type family

       lab is the label for the current goal for tracing purposes
    *)
    let rec cover (cg, w, ccs,  lab, missing) =
        ( chatter 6 (fn () => showPendingCGoal (cg, lab) ^ "\n");
          cover' (contract(cg, lab), w, ccs, lab, missing) )
    and cover' (SOME(cg), w, ccs, lab, missing) =
        let let cands = match (cg, ccs) (* determine splitting candidates *)
            let cand = selectCand cands (* select one candidate *)
        in split (cg, cand, w, ccs, lab, missing) end
      | cover' (NONE, w, ccs, lab, missing) =
        (* cg is covered by unique output inconsistency *)
        ( chatter 6 (fn () => "Covered\n");
          missing )
    and split (cg, NONE, w, ccs, lab, missing) =
        (* cg is covered: return missing patterns from other cases *)
        ( chatter 6 (fn () => "Covered\n");
          missing )
      | split (cg, SOME(nil), w, ccs, lab, missing) =
        (* no strong candidates: check for finitary splitting candidates *)
        ( chatter 6 (fn () => "No strong candidates --- calculating weak candidates\n");
          splitWeak (cg, finitary (cg, w), w, ccs, lab, missing) )
      | split (cg, SOME((k,_)::ksn), w, ccs, lab, missing) =
        (* some candidates: split first candidate, ignoring multiplicities *)
        (* candidates are in reverse order, so non-index candidates are split first *)
        (* splitVar shows splitting as it happens *)
        ( chatter 6 (fn () => "Splitting on " ^ Int.toString (k) ^ "\n");
          case splitVar (cg, k, w)
            of SOME(cases) => covers (cases, w, ccs, lab, missing)
             | NONE =>
              ( chatter 6 (fn () => "Splitting failed due to generated constraints\n");
                split (cg, SOME(ksn), w, ccs, lab, missing)))

    and splitWeak (cg, nil, w, ccs, lab, missing) =
        ( chatter 6 (fn () => "No weak candidates---case " ^ labToString(lab) ^ " not covered\n");
          cg::missing )
      | splitWeak (cg, ksn, w, ccs, lab, missing) = (* ksn <> nil *)
          split (cg, SOME(findMin ksn::nil), w, ccs, lab, missing)

    and covers (cases, w, ccs, lab, missing) =
        ( chatter 6 (fn () => "Found " ^ Int.toString (List.length cases)
                     ^ pluralize (List.length cases, " case") ^ "\n");
          covers' (cases, 1, w, ccs, lab, missing) )
    and covers' (nil, n, w, ccs, lab, missing) =
        ( chatter 6 (fn () => "All subcases of " ^ labToString(lab) ^ " considered\n");
          missing )
      | covers' (cg::cases', n, w, ccs, lab, missing) =
        let
          let missing1 = cover (cg, w, ccs, Child(lab, n), missing)
        in
          covers' (cases', n+1, w, ccs, lab, missing1)
        end

    (* substToSpine' (s, G, T) = S @ T
       If   G' |- s : G
       then G' |- S : {{G}} a >> a  for arbitrary a
       {{G}} erases void declarations in G
    *)
    let rec substToSpine' = function (I.Shift(n), I.Null, T) -> T
      | (I.Shift(n), G as I.Decl _, T) -> 
          substToSpine' (I.Dot (I.Idx (n+1), I.Shift(n+1)), G, T)
      | (I.Dot(_, s), I.Decl(G, I.NDec _), T) -> 
          (* Skip over NDec's; must be either Undef or Idx [from eta-expansion] *)
          (* Unusable meta-decs are eliminated here *)
          substToSpine' (s, G, T)
      | (I.Dot(I.Exp(U),s), I.Decl(G,V), T) -> 
          substToSpine' (s, G, I.App(U, T))
      | (I.Dot(I.Idx(n),s), I.Decl(G,I.Dec(_,V)), T) -> 
          (* Eta-expand *)
        let
          let (Us,_) = Whnf.whnfEta ((I.Root (I.BVar(n), I.Nil), I.id), (V, I.id))
        in
          substToSpine' (s, G, I.App(I.EClo Us, T))
        end
      | (I.Dot (_, s) , I.Decl (G, I.BDec (_, (L, t))), T) -> 
        (* was: I.Idx in previous line, Sun Jan  5 11:02:19 2003 -fp *)
        (* Treat like I.NDec *)
          (* Attempted fix, didn't work because I don't know how you
             computed splitting candidates for Blocks
             --cs Sat Jan  4 22:38:01 2003
          *)
        substToSpine' (s, G, T)


      (* I.Axp, I.Block(B) or other I.Undef impossible *)

    (* substToSpine (s, G) = S
       If   G' |- s : G
       then G' |- S : {{G}} type

       Note: {{G}} erases void declarations in G
     *)
    let rec substToSpine (s, G) = substToSpine' (s, G, I.Nil)

    (* purify' G = (G', s) where all NDec's have been erased from G
       If    |- G ctx
       then  |- G ctx and  G' |- s : G
    *)
    let rec purify' = function (I.Null) -> (I.Null, I.id)
      | (I.Decl (G, I.NDec _)) -> 
        let let (G', s) = purify' G
          (* G' |- s : G *)
        in
          (G', I.Dot (I.Undef, s))
          (* G' |- _.s : G,_ *)
        end
      | (I.Decl (G, D as I.Dec _)) -> 
        let let (G', s) = purify' G
          (* G' |- s : G *)
          (* G |- D : type *)
        in
          (I.Decl (G', I.decSub(D, s)), I.dot1 s)
          (* G' |- D[s] : type *)
          (* G', D[s] |- 1 : D[s][^] *)
          (* G', D[s] |- s o ^ : G *)
          (* G', D[s] |- 1.s o ^ : G, D *)
        end
      (* added a new case to throw out blocks
         -cs Sat Jan  4 22:55:12 2003
      *)
      | (I.Decl (G, D as I.BDec _)) -> 
        let let (G', s) = purify' G
          (* G' |- s : G *)
        in
          (G', I.Dot (I.Undef, s))
          (* G' |- _.s : G,_ *)
        end

    (* purify G = G' where all NDec's have been erased from G
       If   |- G ctx
       then |- G' ctx
    *)
    let rec purify (G) = #1 (purify' G)

    (* coverageCheckCases (W, Cs, G) = R

       Invariant:
       If   Cs = [(G1, s1) .... (Gn, sn)]
       and  Gi |- si : G
       and  for all worlds Phi
       and  instantiations Phi |- s : G
       there exists at least one index k and substitution   Phi |- t : Gk
       s.t.  sk o t = s
    *)
    let rec coverageCheckCases (w, Cs, G) =
        let
          let _ = chatter 4 (fn () => "[Tomega coverage checker...")
          let _ = chatter 4 (fn () => "\n")
          let ccs = List.map (fn (Gi, si) => CClause (Gi, substToSpine (si, G))) Cs
          (* Question: are all the Gi's above named already? *)
          let _ = chatter 6 (fn () => "[Begin covering clauses]\n")
          let _ = List.app (fun cc -> chatter 6 (fn () => showCClause cc ^ "\n")) ccs
          let _ = chatter 6 (fn () => "[End covering clauses]\n")
          let pureG = purify (G)
          let namedG = N.ctxLUName (pureG)
          let R0 = substToSpine (I.id, namedG)
          let cg0 = CGoal (namedG, R0)
          let missing = cover (cg0, w, ccs, Top, nil)
          let _ = case missing
                    of nil => ()        (* all cases covered *)
                     | _::_ => raise Error ("Coverage error")
          let _ = chatter 4 (fn () => "]\n")
        in
          ()
        end

  end
end;; (* functor Cover *)
