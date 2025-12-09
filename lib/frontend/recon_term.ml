(* Type Reconstruction with Tracing *)
(* Author: Kevin Watkins *)
(* Based on a previous implementation by Frank Pfenning *)
(* with modifications by Jeff Polakow and Roberto Virga *)

(* ------------------- *)
(* Type Reconstruction *)
(* ------------------- *)

module ReconTerm ((*! module IntSyn' : INTSYN !*)
                   (Names : NAMES)
                   (*! sharing Names.IntSyn = IntSyn' !*)
                   (*! module Paths' : PATHS !*)
                   (Approx : APPROX)
                   (*! sharing Approx.IntSyn = IntSyn' !*)
                   (Whnf : WHNF)
                   (*! sharing Whnf.IntSyn = IntSyn' !*)
                   (Unify : UNIFY)
                   (*! sharing Unify.IntSyn = IntSyn' !*)
                   (Abstract : ABSTRACT)
                   (*! sharing Abstract.IntSyn = IntSyn' !*)
                   (Print : PRINT)
                   (*! sharing Print.IntSyn = IntSyn' !*)
                   (*! (CSManager : CS_MANAGER) !*)
                   (*! sharing CSManager.IntSyn = IntSyn' !*)
                   (StringTree : TABLE with type key = string)
                   (Msg : MSG)
  : RECON_TERM =
struct

  (*! module IntSyn = IntSyn' !*)
  (*! module Paths = Paths' !*)
  module F = Print.Formatter
  module Apx = Approx

  (* Error handling *)

  let delayedList : (unit -> unit) list ref = ref nil

  let rec clearDelayed () = (delayedList := nil)
  let rec addDelayed f = (delayedList := f::(!delayedList))
  let rec runDelayed () =
      let
        let rec run' = function nil -> ()
          | (h::t) -> (run' t; h ())
      in
        run' (!delayedList)
      end

  exception Error of string

  let errorCount = ref 0
  let errorFileName = ref "no file"

  let errorThreshold = ref (SOME (20))
  let rec exceeds = function (i, NONE) -> false
    | (i, SOME(j)) -> i > j

  let rec resetErrors (fileName) =
      (errorCount := 0;
       errorFileName := fileName)

  let rec die (r) =
        raise Error (Paths.wrap (r,
                     " " ^ Int.toString (!errorCount)
                     ^ " error" ^ (if !errorCount > 1 then "s" else "")
                     ^ " found"))

  let rec checkErrors (r) =
       if !errorCount > 0 then die (r) else ()

  (* Since this module uses a non-standard error reporting mechanism,
     any errors reported here while chatter = 1 will be printed
     in between the "[Loading file ..." message and the closing "]",
     instead of after the closing "]".  If we don't emit a newline
     when chatter = 1, the first such error will appear on the same line
     as "[Loading file ...", terribly confusing the Emacs error parsing code.
   *)
  let rec chatterOneNewline () =
      if !Global.chatter = 1 andalso !errorCount = 1
        then Msg.message "\n"
      else ()

  let rec fatalError (r, msg) =
      (errorCount := !errorCount + 1;
       chatterOneNewline ();
       Msg.message (!errorFileName ^ ":" ^ Paths.wrap (r, msg) ^ "\n");
       die (r))

  let rec error (r, msg) =
      (errorCount := !errorCount + 1;
       chatterOneNewline ();
       Msg.message (!errorFileName ^ ":" ^ Paths.wrap (r, msg) ^ "\n");
       if exceeds (!errorCount, !errorThreshold)
          then die (r)
       else ())

  let rec formatExp (G, U) =
      Print.formatExp (G, U)
      handle Names.Unprintable => F.String "%_unprintable_%"

  (* this is a hack, i know *)
  let queryMode = ref false

  local
    open IntSyn
  in

  let rec headConDec = function (Const c) -> sgnLookup c
    | (Skonst c) -> sgnLookup c
    | (Def d) -> sgnLookup d
    | (NSDef d) -> sgnLookup d
    | (FgnConst (_, cd)) -> cd
      (* others impossible by invariant *)

  (* lowerType (G, (V, s)) = (G', a)
     if   G0 |- V : type and G |- s : G0
     and  G |- V[s] = {{G1}} a : type
     then G' = G, G1 *)
  let rec lowerTypeW = function (G, (Pi ((D, _), V), s)) -> 
      let
        let D' = decSub (D, s)
      in
        lowerType (Decl (G, D'), (V, dot1 s))
      end
    | (G, Vs) -> (G, EClo Vs)
  and lowerType (G, Vs) = lowerTypeW (G, Whnf.whnfExpandDef Vs)

  (* raiseType (G, V) = {{G}} V *)
  let rec raiseType = function (Null, V) -> V
    | (Decl (G, D), V) -> raiseType (G, Pi ((D, Maybe), V))

  end (* open IntSyn *)

  local
    let evarApxTable : Apx.Exp StringTree.Table = StringTree.new (0)
    let fvarApxTable : Apx.Exp StringTree.Table = StringTree.new (0)

    let fvarTable : IntSyn.exp StringTree.Table = StringTree.new (0)
  in

    let rec varReset () = (StringTree.clear evarApxTable;
                       StringTree.clear fvarApxTable;
                       StringTree.clear fvarTable)

    let rec getEVarTypeApx name =
        (case StringTree.lookup evarApxTable name
           of SOME V => V
            | NONE =>
        (case Names.getEVarOpt name
           of SOME (IntSyn.EVar (_, _, V, _)) =>
              let
                let (V', _ (* Type *)) = Apx.classToApx (V)
              in
                StringTree.insert evarApxTable (name, V');
                V'
              end
            | NONE =>
              let
                let V = Apx.newCVar ()
              in
                StringTree.insert evarApxTable (name, V);
                V
              end))

    let rec getFVarTypeApx name =
        (case StringTree.lookup fvarApxTable name
           of SOME V => V
            | NONE =>
              let
                let V = Apx.newCVar ()
              in
                StringTree.insert fvarApxTable (name, V);
                V
              end)

    let rec getEVar (name, allowed) =
        (case Names.getEVarOpt name
           of SOME (X as IntSyn.EVar (_, G, V, _)) => (X, raiseType (G, V))
            | NONE =>
              let
                let V = Option.valOf (StringTree.lookup evarApxTable name)
                let V' = Apx.apxToClass (IntSyn.Null, V, Apx.Type, allowed)
                let (G'', V'') = lowerType (IntSyn.Null, (V', IntSyn.id))
                let X = IntSyn.newEVar (G'', V'')
              in
                Names.addEVar (X, name);
                (X, V')
              end)

    let rec getFVarType (name, allowed) =
        (case StringTree.lookup fvarTable name
           of SOME V => V
            | NONE =>
              let
                let V = Option.valOf (StringTree.lookup fvarApxTable name)
                let V' = Apx.apxToClass (IntSyn.Null, V, Apx.Type, allowed)
              in
                StringTree.insert fvarTable (name, V');
                V'
              end)

  end

  (* External syntax of terms *)

  type term =
      internal of IntSyn.exp * IntSyn.exp * Paths.region (* (U, V, r) *)
        (* G |- U : V nf where V : L or V == kind *)
        (* not used currently *)

    | constant of IntSyn.Head * Paths.region
        (* must be Const/Skonst/Def/NSDef/FgnConst *)
    | bvar of int * Paths.region
    | evar of string * Paths.region
    | fvar of string * Paths.region
    | typ of Paths.region
    | arrow of term * term
    | pi of dec * term
    | lam of dec * term
    | app of term * term
    | hastype of term * term
    | mismatch of term * term * string * string
        (* (original, replacement, location, problem) *)

      (* Phase 1 only *)
    | omitted of Paths.region
    | lcid of string list * string * Paths.region
    | ucid of string list * string * Paths.region
    | quid of string list * string * Paths.region
    | scon of string * Paths.region

      (* Phase 2 only *)
    | omitapx of Apx.Exp * Apx.Exp * Apx.Uni * Paths.region
        (* (U, V, L, r) where U ~:~ V ~:~ L *)
        (* U undefined unless L >= kind *)

      (* Phase 3 only *)
    | omitexact of IntSyn.exp * IntSyn.exp * Paths.region

  and dec =
      dec of string option * term * Paths.region

  let rec backarrow (tm1, tm2) = arrow (tm2, tm1)

  (* for now *)
  let rec dec0 (nameOpt, r) = dec (nameOpt, omitted (r), r)

  type job =
      jnothing
    | jand of job * job
    | jwithctx of dec IntSyn.ctx * job
    | jterm of term
    | jclass of term
    | jof of term * term
    | jof' of term * IntSyn.exp

  let rec termRegion = function (internal (U, V, r)) -> r
    | (constant (H, r)) -> r
    | (bvar (k, r)) -> r
    | (evar (name, r)) -> r
    | (fvar (name, r)) -> r
    | (typ (r)) -> r
    | (arrow (tm1, tm2)) -> 
        Paths.join (termRegion tm1, termRegion tm2)
    | (pi (tm1, tm2)) -> 
        Paths.join (decRegion tm1, termRegion tm2)
    | (lam (tm1, tm2)) -> 
        Paths.join (decRegion tm1, termRegion tm2)
    | (app (tm1, tm2)) -> 
        Paths.join (termRegion tm1, termRegion tm2)
    | (hastype (tm1, tm2)) -> 
        Paths.join (termRegion tm1, termRegion tm2)
    | (mismatch (tm1, tm2, _, _)) -> 
        termRegion tm2
    | (omitted (r)) -> r
    | (lcid (_, _, r)) -> r
    | (ucid (_, _, r)) -> r
    | (quid (_, _, r)) -> r
    | (scon (_, r)) -> r
    | (omitapx (U, V, L, r)) -> r
    | (omitexact (U, V, r)) -> r

  and decRegion (dec (name, tm, r)) = r

  let rec ctxRegion = function (IntSyn.Null) -> NONE
    | (IntSyn.Decl (g, tm)) -> 
        ctxRegion' (g, decRegion tm)

  and ctxRegion' (IntSyn.Null, r) = SOME r
    | ctxRegion' (IntSyn.Decl (g, tm), r) =
        ctxRegion' (g, Paths.join (r, decRegion tm))

  local
    open Apx
    type Ctx = type IntSyn.ctx
    type Dec = Dec of string option * Exp | NDec of string option
  in

    (* Phase 1:
       Try to determine an approximate type/kind and level for each subterm.
       In cases where there's a mismatch, it's generally better not to report
       it immediately, but rather to wait until after the exact phase, so that
       the error message can mention more precise type information.  So instead
       the bad subterm is wrapped in a `mismatch' constructor, which also
       supplies a replacement (always an `omitted' in the current implementation)
       so that the invariant that the entire term is approximately well-typed
       after phase 1 is satisfied even in the presence of the error.
     *)

    (* inferApx (G, tm, false) = (tm', U, V, L)
       pre: G is an approximate context
            tm is an approximate subject
       post: tm' is an approximate subject
             U is an approximate subject
             V is an approximate classifier
             L is an approximate universe
             G |- U ~:~ V ~:~ L
             termToExp tm' = U

       inferApx (G, tm, true) = (tm', U, V, L)
       pre: G is an approximate context
            tm is an approximate classifier
       post: tm' is an approximate classifier
             U is an approximate classifier
             V is an approximate classifier
             L is an approximate universe
             G |- U ~:~ V ~:~ L
             termToExp tm' = U
     *)

    let rec filterLevel (tm, L, max, msg) =
        let
          let notGround = makeGroundUni L
          let Level i = whnfUni L
        in
          if i > max
          then fatalError (termRegion tm,
                           "Level too high\n" ^ msg)
          else if notGround
          then error (termRegion tm,
                      "Ambiguous level\n" ^
                      "The level of this term could not be inferred\n" ^
                      "Defaulting to " ^
                      (case i
                         of 1 => "object"
                          | 2 => "type family"
                          | 3 => "kind") ^
                      " level")
          else ()
        end

    let rec findOmitted (G, qid, r) =
          (error (r, "Undeclared identifier "
                     ^ Names.qidToString (valOf (Names.constUndef qid)));
           omitted (r))

    let rec findBVar' = function (Null, name, k) -> NONE
      | (Decl (G, Dec (NONE, _)), name, k) -> 
          findBVar' (G, name, k+1)
      | (Decl (G, NDec _), name, k) -> 
          findBVar' (G, name, k+1)
      | (Decl (G, Dec (SOME(name'), _)), name, k) -> 
          if name = name' then SOME (k)
          else findBVar' (G, name, k+1)

    let rec findBVar fc (G, qid, r) =
        (case Names.unqualified qid
           of NONE => fc (G, qid, r)
            | SOME name =>
              (case findBVar' (G, name, 1)
                 of NONE => fc (G, qid, r)
                  | SOME k => bvar (k, r)))

    let rec findConst fc (G, qid, r) =
        (case Names.constLookup qid
           of NONE => fc (G, qid, r)
            | SOME cid =>
              (case IntSyn.sgnLookup cid
                 of IntSyn.ConDec _ => constant (IntSyn.Const cid, r)
                  | IntSyn.ConDef _ => constant (IntSyn.Def cid, r)
                  | IntSyn.AbbrevDef _ => constant (IntSyn.NSDef cid, r)
                  | _ =>
                    (error (r, "Invalid identifier\n"
                            ^ "Identifier `" ^ Names.qidToString qid
                            ^ "' is not a constant, definition or abbreviation");
                     omitted (r))))

    let rec findCSConst fc (G, qid, r) =
        (case Names.unqualified qid
           of NONE => fc (G, qid, r)
            | SOME name =>
              (case CSManager.parse name
                 of NONE => fc (G, qid, r)
                  | SOME (cs, conDec) =>
                      constant (IntSyn.FgnConst (cs, conDec), r)))

    let rec findEFVar fc (G, qid, r) =
        (case Names.unqualified qid
           of NONE => fc (G, qid, r)
            | SOME name => (if !queryMode then evar else fvar) (name, r))

    let rec findLCID x = findBVar (findConst (findCSConst findOmitted)) x
    let rec findUCID x = findBVar (findConst (findCSConst (findEFVar findOmitted))) x
    let rec findQUID x = findConst (findCSConst findOmitted) x


    let rec inferApx = function (G, tm as internal (U, V, r)) -> 
        let
          let (U', V', L') = exactToApx (U, V)
        in
          (tm, U', V', L')
        end

      | (G, tm as lcid (ids, name, r)) -> 
        let
          let qid = Names.Qid (ids, name)
        in
          inferApx (G, findLCID (G, qid, r))
        end
      | (G, tm as ucid (ids, name, r)) -> 
        let
          let qid = Names.Qid (ids, name)
        in
          inferApx (G, findUCID (G, qid, r))
        end
      | (G, tm as quid (ids, name, r)) -> 
        let
          let qid = Names.Qid (ids, name)
        in
          inferApx (G, findQUID (G, qid, r))
        end
      | (G, tm as scon (name, r)) -> 
          (case CSManager.parse name
             of NONE => (error (r, "Strings unsupported in current module type");
                         inferApx (G, omitted (r)))
              | SOME (cs, conDec) =>
                  inferApx (G, constant (IntSyn.FgnConst (cs, conDec), r)))

      | (G, tm as constant (H, r)) -> 
        let
          let cd = headConDec H
          let (U', V', L') = exactToApx (IntSyn.Root (H, IntSyn.Nil),
                                         IntSyn.conDecType cd)
          let rec dropImplicit (V, 0) = V
            | dropImplicit (Arrow (_, V), i) = dropImplicit (V, i-1)
          let V'' = dropImplicit (V', IntSyn.conDecImp cd)
        in
          (tm, U', V'', L')
        end
      | (G, tm as bvar (k, r)) -> 
        let
          let Dec (_, V) = IntSyn.ctxLookup (G, k)
        in
          (tm, Undefined, V, Type)
        end
      | (G, tm as evar (name, r)) -> 
          (tm, Undefined, getEVarTypeApx name, Type)
      | (G, tm as fvar (name, r)) -> 
          (tm, Undefined, getFVarTypeApx name, Type)
      | (G, tm as typ (r)) -> 
          (tm, Uni Type, Uni Kind, Hyperkind)
      | (G, arrow (tm1, tm2)) -> 
        let
          let L = newLVar ()
          let (tm1', V1) = checkApx (G, tm1, Uni Type, Kind,
                                     "Left-hand side of arrow must be a type")
          let (tm2', V2) = checkApx (G, tm2, Uni L, Next L,
                                     "Right-hand side of arrow must be a type or a kind")
        in
          (arrow (tm1', tm2'), Arrow (V1, V2), Uni L, Next L)
        end
      | (G, pi (tm1, tm2)) -> 
        let
          let (tm1', D as Dec (_, V1)) = inferApxDec (G, tm1)
          let L = newLVar ()
          let (tm2', V2) = checkApx (Decl (G, D), tm2, Uni L, Next L,
                                     "Body of pi must be a type or a kind")
        in
          (pi (tm1', tm2'), Arrow (V1, V2), Uni L, Next L)
        end
      | (G, tm as lam (tm1, tm2)) -> 
        let
          let (tm1', D as Dec (_, V1)) = inferApxDec (G, tm1)
          let (tm2', U2, V2, L2) = inferApx (Decl (G, D), tm2)
        in
          (lam (tm1', tm2'), U2, Arrow (V1, V2), L2)
        end
      | (G, tm as app (tm1, tm2)) -> 
        let
          let L = newLVar ()
          let Va = newCVar ()
          let Vr = newCVar ()
          let (tm1', U1) = checkApx (G, tm1, Arrow (Va, Vr), L,
                                     "Non-function was applied to an argument")
          (* probably a confusing message if the problem is the level: *)
          let (tm2', _) = checkApx (G, tm2, Va, Type,
                                    "Argument type did not match function domain type")
        in
          (app (tm1', tm2'), U1, Vr, L)
        end
      | (G, tm as hastype (tm1, tm2)) -> 
        let
          let L = newLVar ()
          let (tm2', V2) = checkApx (G, tm2, Uni L, Next L,
                                     "Right-hand side of ascription must be a type or a kind")
          let (tm1', U1) = checkApx (G, tm1, V2, L,
                                     "Ascription did not hold")
          let _ = addDelayed (fn () => filterLevel (tm, L, 2, "Ascription can only be applied to objects and type families"))
        in
          (hastype (tm1', tm2'), U1, V2, L)
        end
      | (G, omitted (r)) -> 
        let
          let L = newLVar ()
          let V = newCVar ()
          let U = newCVar () (* guaranteed not to be used if L is type *)
        in
          (omitapx (U, V, L, r), U, V, L)
        end

    and checkApx (G, tm, V, L, location_msg) =
        let
          let (tm', U', V', L') = inferApx (G, tm)
        in
          (matchUni (L, L'); match (V, V'); (tm', U'))
          handle Unify problem_msg =>
          let
            let r = termRegion tm
            let (tm'', U'') = checkApx (G, omitted (r), V, L, location_msg)
            (* just in case *)
            let _ = addDelayed (fn () => (makeGroundUni L'; ()))
          in
            (mismatch (tm', tm'', location_msg, problem_msg), U'')
          end
        end

    and inferApxDec (G, dec (name, tm, r)) =
        let
          let (tm', V1) = checkApx (G, tm, Uni Type, Kind,
                                    "Classifier in declaration must be a type")
          let D = Dec (name, V1)
        in
          (dec (name, tm', r), D)
        end

    let rec inferApxJob = function (G, jnothing) -> jnothing
      | (G, jand (j1, j2)) -> 
          jand (inferApxJob (G, j1), inferApxJob (G, j2))
      | (G, jwithctx (g, j)) -> 
        let
          let rec ia (Null) = (G, Null)
            | ia (Decl (g, tm)) =
              let
                let (G', g') = ia (g)
                let _ = clearDelayed ()
                let (tm', D) = inferApxDec (G', tm)
                let _ = runDelayed ()
              in
                (Decl (G', D), Decl (g', tm'))
              end
          let (G', g') = ia (g)
        in
          jwithctx (g', inferApxJob (G', j))
        end
      | (G, jterm (tm)) -> 
        let
          let _ = clearDelayed ()
          let (tm', U, V, L) = inferApx (G, tm)
          let _ = filterLevel (tm', L, 2,
                               "The term in this position must be an object or a type family")
          let _ = runDelayed ()
        in
          jterm (tm')
        end
      | (G, jclass (tm)) -> 
        let
          let _ = clearDelayed ()
          let L = newLVar ()
          let (tm', V) = checkApx (G, tm, Uni L, Next L,
                                   "The term in this position must be a type or a kind")
          let _ = filterLevel (tm', Next L, 3,
                               "The term in this position must be a type or a kind")
          let _ = runDelayed ()
        in
          jclass (tm')
        end
      | (G, jof (tm1, tm2)) -> 
        let
          let _ = clearDelayed ()
          let L = newLVar ()
          let (tm2', V2) = checkApx (G, tm2, Uni L, Next L,
                                     "The term in this position must be a type or a kind")
          let (tm1', U1) = checkApx (G, tm1, V2, L,
                                     "Ascription in declaration did not hold")
          let _ = filterLevel (tm1', L, 2,
                               "The term in this position must be an object or a type family")
          let _ = runDelayed ()
        in
          jof (tm1', tm2')
        end
      | (G, jof' (tm1, V)) -> 
        let
          let _ = clearDelayed ()
          let L = newLVar ()
          let (V2, _) = Apx.classToApx V
          let (tm1', U1) = checkApx (G, tm1, V2, L,
                                     "Ascription in declaration did not hold")
          let _ = filterLevel (tm1', L, 2,
                               "The term in this position must be an object or a type family")
          let _ = runDelayed ()
        in
          jof' (tm1', V)
        end

    let rec ctxToApx = function IntSyn.Null -> IntSyn.Null
      | (IntSyn.Decl (G, IntSyn.NDec x)) -> 
          IntSyn.Decl (ctxToApx G, NDec x)
      | (IntSyn.Decl (G, IntSyn.Dec (name, V))) -> 
          let
            let (V', _) = Apx.classToApx V
          in
            IntSyn.Decl (ctxToApx G, Dec (name, V'))
          end

    let rec inferApxJob' (G, t) =
        inferApxJob (ctxToApx G, t)

  end (* open Apx *)

  local
    open IntSyn
  in

  (* Final reconstruction job syntax *)

  type job =
      JNothing
    | JAnd of Job * Job
    | JWithCtx of IntSyn.Dec IntSyn.ctx * Job
    | JTerm of (IntSyn.exp * Paths.occExp) * IntSyn.exp * IntSyn.Uni
    | JClass of (IntSyn.exp * Paths.occExp) * IntSyn.Uni
    | JOf of (IntSyn.exp * Paths.occExp) * (IntSyn.exp * Paths.occExp) * IntSyn.Uni

  (* This little type makes it easier to work with eta-expanded terms
     The idea is that Elim E represents a term U if
       E (s, S) = U[s] @ S *)

  type bidi =
      Elim of IntSyn.Sub * IntSyn.Spine -> IntSyn.exp
    | Intro of IntSyn.exp

  let rec elimSub (E, s) = (fn (s', S) => E (comp (s, s'), S))
  let rec elimApp (E, U) = (fn (s, S) => E (s, App (EClo (U, s), S)))

  let rec bvarElim (n) = (fn (s, S) =>
      (case bvarSub (n, s)
         of Idx (n') => Root (BVar n', S)
          | Exp (U) => Redex (U, S)))
  let rec fvarElim (name, V, s) =
        (fn (s', S) => Root (FVar (name, V, comp (s, s')), S))
  let rec redexElim (U) = (fn (s, S) => Redex (EClo (U, s), S))
  (* headElim (H) = E
     assumes H not Proj _ *)
  let rec headElim = function (BVar n) -> bvarElim n
    | (FVar fv) -> fvarElim fv
    | (NSDef d) -> redexElim (constDef d)
    | (H) -> 
      (case conDecStatus (headConDec H)
         of Foreign (csid, f) => (fn (s, S) => f S)
          | _ => (fn (s, S) => Root (H, S)))
  (* although internally EVars are lowered intro forms, externally they're
     raised elim forms.
     this conforms to the external interpretation:
     the type of the returned elim form is ([[G]] V) *)
  let rec evarElim (X as EVar _) =
        (fn (s, S) => EClo (X, Whnf.spineToSub (S, s)))

  let rec etaExpandW = function (E, (Pi ((D as Dec (_, Va), _), Vr), s)) -> 
      let
        let U1 = etaExpand (bvarElim (1), (Va, comp (s, shift)))
        let D' = decSub (D, s)
      in
        Lam (D', etaExpand (elimApp (elimSub (E, shift), U1), (Vr, dot1 s)))
      end
    | (E, _) -> E (id, Nil)
  and etaExpand (E, Vs) = etaExpandW (E, Whnf.whnfExpandDef Vs)

  (* preserves redices *)
  let rec toElim = function (Elim E) -> E
    | (Intro U) -> redexElim U

  let rec toIntro = function (Elim E, Vs) -> etaExpand (E, Vs)
    | (Intro U, Vs) -> U

  let rec addImplicit1W (G, E, (Pi ((Dec (_, Va), _), Vr), s), i (* >= 1 *)) =
      let
        let X = Whnf.newLoweredEVar (G, (Va, s))
      in
        addImplicit (G, elimApp (E, X), (Vr, Whnf.dotEta (Exp (X), s)), i-1)
      end

      (* if no implicit arguments, do not expand Vs!!! *)
  and addImplicit (G, E, Vs, 0) = (E, EClo Vs)
    | addImplicit (G, E, Vs, i) = addImplicit1W (G, E, Whnf.whnfExpandDef Vs, i)


  (* Report mismatches after the entire process finishes -- yields better
     error messages *)

  let rec reportConstraints (Xnames) =
      (case Print.evarCnstrsToStringOpt (Xnames)
         of NONE => ()
          | SOME(constr) => print ("Constraints:\n" ^ constr ^ "\n"))
      handle Names.Unprintable => print "%_constraints unprintable_%\n"

  let rec reportInst (Xnames) =
      (Msg.message (Print.evarInstToString (Xnames) ^ "\n"))
      handle Names.Unprintable => Msg.message "%_unifier unprintable_%\n"

  let rec delayMismatch (G, V1, V2, r2, location_msg, problem_msg) =
      addDelayed (fn () =>
      let
        let Xs = Abstract.collectEVars (G, (V2, id),
                 Abstract.collectEVars (G, (V1, id), nil))
        let Xnames = List.map (fun X -> (X, Names.evarName (IntSyn.Null, X))) Xs
        let V1fmt = formatExp (G, V1)
        let V2fmt = formatExp (G, V2)
        let diff = F.Vbox0 0 1
                   [F.String "Expected:", F.Space, V2fmt, F.Break,
                    F.String "Inferred:", F.Space, V1fmt]
        let diff = (case Print.evarCnstrsToStringOpt (Xnames)
                      of NONE => F.makestring_fmt diff
                       | SOME(cnstrs) => F.makestring_fmt diff ^
                                         "\nConstraints:\n" ^ cnstrs)
      in
        error (r2, "Type mismatch\n"
                   ^ diff ^ "\n"
                   ^ problem_msg ^ "\n"
                   ^ location_msg)
      end)

  let rec delayAmbiguous (G, U, r, msg) =
      addDelayed (fn () =>
      let
        let Ufmt = formatExp (G, U)
        let amb = F.HVbox [F.String "Inferred:", F.Space, formatExp (G, U)]
      in
        error (r, "Ambiguous reconstruction\n"
                  ^ F.makestring_fmt amb ^ "\n"
                  ^ msg)
      end)

  let rec unifyIdem x =
      let
        (* this reset should be unnecessary -- for safety only *)
        let _ = Unify.reset ()
        let _ = Unify.unify x
                handle e as Unify.Unify _ =>
                       (Unify.unwind ();
                        raise e)
        let _ = Unify.reset ()
      in
        ()
      end

  let rec unifiableIdem x =
      let
        (* this reset should be unnecessary -- for safety only *)
        let _ = Unify.reset ()
        let ok = Unify.unifiable x
        let _ = if ok then Unify.reset () else Unify.unwind ()
      in
        ok
      end

  (* tracing code *)

  type traceMode = Progressive | Omniscient
  let trace = ref false
  let traceMode = ref Omniscient

  let rec report f = case !traceMode of Progressive => f ()
                                  | Omniscient => addDelayed f

  let rec reportMismatch (G, Vs1, Vs2, problem_msg) =
      report (fn () =>
      let
        let Xs = Abstract.collectEVars (G, Vs2,
                 Abstract.collectEVars (G, Vs1, nil))
        let Xnames = List.map (fun X -> (X, Names.evarName (IntSyn.Null, X))) Xs
        let eqnsFmt = F.HVbox [F.String "|?", F.Space, formatExp (G, EClo Vs1),
                               F.Break, F.String "=", F.Space, formatExp (G, EClo Vs2)]
        let _ = Msg.message (F.makestring_fmt eqnsFmt ^ "\n")
        let _ = reportConstraints Xnames
        let _ = Msg.message ("Failed: " ^ problem_msg ^ "\n"
                       ^ "Continuing with subterm replaced by _\n")
      in
        ()
      end)

  let rec reportUnify' (G, Vs1, Vs2) =
      let
        let Xs = Abstract.collectEVars (G, Vs2,
                 Abstract.collectEVars (G, Vs1, nil))
        let Xnames = List.map (fun X -> (X, Names.evarName (IntSyn.Null, X))) Xs
        let eqnsFmt = F.HVbox [F.String "|?", F.Space, formatExp (G, EClo Vs1),
                               F.Break, F.String "=", F.Space, formatExp (G, EClo Vs2)]
        let _ = Msg.message (F.makestring_fmt eqnsFmt ^ "\n")
        let _ = unifyIdem (G, Vs1, Vs2)
                handle e as Unify.Unify msg =>
                       (Msg.message ("Failed: " ^ msg ^ "\n"
                               ^ "Continuing with subterm replaced by _\n");
                        raise e)
        let _ = reportInst Xnames
        let _ = reportConstraints Xnames
      in
        ()
      end

  let rec reportUnify (G, Vs1, Vs2) =
        (case !traceMode
           of Progressive => reportUnify' (G, Vs1, Vs2)
            | Omniscient =>
                (unifyIdem (G, Vs1, Vs2)
                 handle e as Unify.Unify msg =>
                   (reportMismatch (G, Vs1, Vs2, msg);
                    raise e)))

  let rec reportInfer' = function (G, omitexact (_, _, r), U, V) -> 
      let
        let Xs = Abstract.collectEVars (G, (U, id),
                 Abstract.collectEVars (G, (V, id), nil))
        let Xnames = List.map (fun X -> (X, Names.evarName (IntSyn.Null, X))) Xs
        let omit = F.HVbox [F.String "|-", F.Space, F.String "_", F.Space,
                            F.String "==>", F.Space, formatExp (G, U), F.Break,
                            F.String ":", F.Space, formatExp (G, V)]
        let _ = Msg.message (F.makestring_fmt omit ^ "\n")
        let _ = reportConstraints Xnames
      in
        ()
      end
    | (G, mismatch (tm1, tm2, _, _), U, V) -> 
        reportInfer' (G, tm2, U, V)
    | (G, hastype _, U, V) -> ()
    | (G, tm, U, V) -> 
      let
        let Xs = Abstract.collectEVars (G, (U, id),
                 Abstract.collectEVars (G, (V, id), nil))
        let Xnames = List.map (fun X -> (X, Names.evarName (IntSyn.Null, X))) Xs
        let judg = F.HVbox [F.String "|-", F.Space, formatExp (G, U), F.Break,
                            F.String ":", F.Space, formatExp (G, V)]
        let _ = Msg.message (F.makestring_fmt judg ^ "\n")
        let _ = reportConstraints Xnames
      in
        ()
      end

  let rec reportInfer x = report (fn () => reportInfer' x)


    (* inferExact (G, tm) = (tm', U, V)
       if  tm is approximately well typed
       and tm contains no subterm above kind level
       and tm ~:~ V1
       then tm = U-
       and  U : V
       and  U, V are most general such
       effect: as for unification *)

    let rec inferExactN = function (G, tm as internal (U, V, r)) -> 
          (tm, Intro U, V)
      | (G, tm as constant (H, r)) -> 
        let
          let cd = headConDec (H)
          let (E, V) = addImplicit (G, headElim H, (conDecType cd, id), conDecImp cd)
        in
          (tm, Elim E, V)
        end
      | (G, tm as bvar (k, r)) -> 
        let
          let Dec (_, V) = ctxDec (G, k)
        in
          (tm, Elim (bvarElim k), V)
        end
      | (G, tm as evar (name, r)) -> 
        let
          (* externally EVars are raised elim forms *)
          let (X, V) = getEVar (name, false)
                  handle Apx.Ambiguous =>
                  let
                    let (X, V) = getEVar (name, true)
                  in
                    delayAmbiguous (G, V, r, "Free variable has ambiguous type");
                    (X, V)
                  end
          let s = Shift (ctxLength (G)) (* necessary? -kw *)
        in
          (tm, Elim (elimSub (evarElim X, s)), EClo (V, s))
        end
      | (G, tm as fvar (name, r)) -> 
        let
          let V = getFVarType (name, false)
                  handle Apx.Ambiguous =>
                  let
                    let V = getFVarType (name, true)
                  in
                    delayAmbiguous (G, V, r, "Free variable has ambiguous type");
                    V
                  end
          let s = Shift (ctxLength (G)) (* necessary? -kw *)
        in
          (tm, Elim (fvarElim (name, V, s)), EClo (V, s))
        end
      | (G, tm as typ (r)) -> 
          (tm, Intro (Uni Type), Uni Kind)
      | (G, arrow (tm1, tm2)) -> 
        let
          let (tm1', B1, _ (* Uni Type *)) = inferExact (G, tm1)
          let D = Dec (NONE, toIntro (B1, (Uni Type, id)))
          let (tm2', B2, L) = inferExact (G, tm2)
          let V2 = toIntro (B2, (L, id))
        in
          (arrow (tm1', tm2'), Intro (Pi ((D, No), EClo (V2, shift))), L)
        end
      | (G, pi (tm1, tm2)) -> 
        let
          let (tm1', D) = inferExactDec (G, tm1)
          let (tm2', B2, L) = inferExact (Decl (G, D), tm2)
          let V2 = toIntro (B2, (L, id))
        in
          (pi (tm1', tm2'), Intro (Pi ((D, Maybe), V2)), L)
        end
      | (G, lam (tm1, tm2)) -> 
        let
          let (tm1', D) = inferExactDec (G, tm1)
          let (tm2', B2, V2) = inferExact (Decl (G, D), tm2)
          let U2 = toIntro (B2, (V2, id))
        in
          (lam (tm1', tm2'), Intro (Lam (D, U2)), Pi ((D, Maybe), V2))
        end
      | (G, app (tm1, tm2)) -> 
        let
          let (tm1', B1, V1) = inferExact (G, tm1)
          let E1 = toElim (B1)
          let (Pi ((Dec (_, Va), _), Vr), s) = Whnf.whnfExpandDef (V1, id)
          let (tm2', B2) = checkExact (G, tm2, (Va, s),
                                       "Argument type did not match function domain type\n(Index object(s) did not match)")
          let U2 = toIntro (B2, (Va, s))
        in
          (app (tm1', tm2'), Elim (elimApp (E1, U2)), EClo (Vr, Whnf.dotEta (Exp U2, s)))
        end
      | (G, hastype (tm1, tm2)) -> 
        let
          let (tm2', B2, L) = inferExact (G, tm2)
          let V = toIntro (B2, (L, id))
          let (tm1', B1) = checkExact (G, tm1, (V, id),
                                      "Ascription did not hold\n(Index object(s) did not match)")
        in
          (hastype (tm1', tm2'), B1, V)
        end
      | (G, mismatch (tm1, tm2, location_msg, problem_msg)) -> 
        let
          let (tm1', _, V1) = inferExact (G, tm1)
          let (tm2', B, V) = inferExactN (G, tm2)
          let _ = if !trace then reportMismatch (G, (V1, id), (V, id), problem_msg) else ()
          let _ = delayMismatch (G, V1, V, termRegion tm2', location_msg, problem_msg)
        in
          (mismatch (tm1', tm2', location_msg, problem_msg), B, V)
        end
      | (G, omitapx (U, V, L, r)) -> 
        let
          let V' = Apx.apxToClass (G, V, L, false)
                   handle Apx.Ambiguous =>
                   let
                     let V' = Apx.apxToClass (G, V, L, true)
                   in
                     delayAmbiguous (G, V', r, "Omitted term has ambiguous " ^
                       (case Apx.whnfUni L
                          of Apx.Level 1 => "type"
                           | Apx.Level 2 => "kind"
                             (* yes, this can happen in pathological cases, e.g.
                                  a : type. b = a : _ _. *)
                             (* FIX: this violates an invariant in printing *)
                           | Apx.Level 3 => "hyperkind"));
                     V'
                   end
          let U' = Apx.apxToExact (G, U, (V', id), false)
                   handle Apx.Ambiguous =>
                   let
                     let U' = Apx.apxToExact (G, U, (V', id), true)
                   in
                     delayAmbiguous (G, U', r, "Omitted " ^
                       (case Apx.whnfUni L
                          of Apx.Level 2 => "type"
                           | Apx.Level 3 => "kind") ^ " is ambiguous");
                     U'
                   end
        in
          (omitexact (U', V', r), Intro U', V')
        end

    and inferExact (G, tm) =
        if not (!trace) then inferExactN (G, tm)
        else
        let
          let (tm', B', V') = inferExactN (G, tm)
        in
          reportInfer (G, tm', toIntro (B', (V', id)), V');
          (tm', B', V')
        end

    and inferExactDec (G, dec (name, tm, r)) =
        let
          let (tm', B1, _ (* Uni Type *)) = inferExact (G, tm)
          let V1 = toIntro (B1, (Uni Type, id))
          let D = Dec (name, V1)
        in
          (dec (name, tm', r), D)
        end

    and checkExact1 (G, lam (dec (name, tm1, r), tm2), Vhs) =
        let
          let (Pi ((Dec (_, Va), _), Vr), s) = Whnf.whnfExpandDef Vhs
          let ((tm1', B1, _ (* Uni Type *)), ok1) = unifyExact (G, tm1, (Va, s))
          let V1 = toIntro (B1, (Uni Type, id))
          let D = Dec (name, V1)
          let ((tm2', B2, V2), ok2) =
                if ok1 then checkExact1 (Decl (G, D), tm2, (Vr, dot1 s))
                else (inferExact (Decl (G, D), tm2), false)
          let U2 = toIntro (B2, (V2, id))
        in
          ((lam (dec (name, tm1', r), tm2'), Intro (Lam (D, U2)), Pi ((D, Maybe), V2)), ok2)
        end
      | checkExact1 (G, hastype (tm1, tm2), Vhs) =
        let
          let ((tm2', B2, L), ok2) = unifyExact (G, tm2, Vhs)
          let V = toIntro (B2, (L, id))
          let (tm1', B1) = checkExact (G, tm1, (V, id),
                                       "Ascription did not hold\n(Index object(s) did not match)")
        in
          ((hastype (tm1', tm2'), B1, V), ok2)
        end
      | checkExact1 (G, mismatch (tm1, tm2, location_msg, problem_msg), Vhs) =
        let
          let (tm1', _, V1) = inferExact (G, tm1)
          let ((tm2', B, V), ok2) = checkExact1 (G, tm2, Vhs)
          let _ = delayMismatch (G, V1, V, termRegion tm2', location_msg, problem_msg)
        in
          ((mismatch (tm1', tm2', location_msg, problem_msg), B, V), ok2)
        end
      | checkExact1 (G, omitapx (U, V (* = Vhs *), L, r), Vhs) =
        let
          let V' = EClo Vhs
          let U' = Apx.apxToExact (G, U, Vhs, false)
                   handle Apx.Ambiguous =>
                   let
                     let U' = Apx.apxToExact (G, U, Vhs, true)
                   in
                     delayAmbiguous (G, U', r, "Omitted " ^
                       (case Apx.whnfUni L
                          of Apx.Level 2 => "type"
                           | Apx.Level 3 => "kind") ^ " is ambiguous");
                     U'
                   end
        in
          ((omitexact (U', V', r), Intro U', V'), true)
        end
      | checkExact1 (G, tm, Vhs) =
        let
          let (tm', B', V') = inferExact (G, tm)
        in
          ((tm', B', V'), unifiableIdem (G, Vhs, (V', id)))
        end

    and checkExact (G, tm, Vs, location_msg) =
        if not (!trace) then
        let
          let ((tm', B', V'), ok) = checkExact1 (G, tm, Vs)
        in
          if ok then (tm', B')
          else
          ((unifyIdem (G, (V', id), Vs);
            raise Match (* can't happen *))
           handle Unify.Unify problem_msg =>
           let
             let r = termRegion tm
             let U' = toIntro (B', (V', id))
             let (Uapx, Vapx, Lapx) = Apx.exactToApx (U', V')
             let ((tm'', B'', _ (* Vs *)), _ (* true *)) =
                   checkExact1 (G, omitapx (Uapx, Vapx, Lapx, r), Vs)
             let _ = delayMismatch (G, V', EClo Vs, r, location_msg, problem_msg)
           in
             (mismatch (tm', tm'', location_msg, problem_msg), B'')
           end)
        end

        else
        let
          let (tm', B', V') = inferExact (G, tm)
        in
          (reportUnify (G, (V', id), Vs); (tm', B'))
          handle Unify.Unify problem_msg =>
          let
            let r = termRegion tm
            let U' = toIntro (B', (V', id))
            let (Uapx, Vapx, Lapx) = Apx.exactToApx (U', V')
            let (tm'', B'') =
                  checkExact (G, omitapx (Uapx, Vapx, Lapx, r), Vs, location_msg)
            let _ = delayMismatch (G, V', EClo Vs, r, location_msg, problem_msg)
          in
            (mismatch (tm', tm'', location_msg, problem_msg), B'')
          end
        end

    and unifyExact (G, arrow (tm1, tm2), Vhs) =
        let
          let (Pi ((Dec (_, Va), _), Vr), s) = Whnf.whnfExpandDef Vhs
          let ((tm1', B1, _ (* Uni Type *)), ok1) = unifyExact (G, tm1, (Va, s))
          let V1 = toIntro (B1, (Uni Type, id))
          let D = Dec (NONE, V1)
          let (tm2', B2, L) = inferExact (G, tm2)
          let V2 = toIntro (B2, (L, id))
        in
          ((arrow (tm1', tm2'), Intro (Pi ((D, No), EClo (V2, shift))), L),
           ok1 andalso unifiableIdem (Decl (G, D), (Vr, dot1 s), (V2, shift)))
        end
      | unifyExact (G, pi (dec (name, tm1, r), tm2), Vhs) =
        let
          let (Pi ((Dec (_, Va), _), Vr), s) = Whnf.whnfExpandDef Vhs
          let ((tm1', B1, _ (* Uni Type *)), ok1) = unifyExact (G, tm1, (Va, s))
          let V1 = toIntro (B1, (Uni Type, id))
          let D = Dec (name, V1)
          let ((tm2', B2, L), ok2) =
                if ok1 then unifyExact (Decl (G, D), tm2, (Vr, dot1 s))
                else (inferExact (Decl (G, D), tm2), false)
          let V2 = toIntro (B2, (L, id))
        in
          ((pi (dec (name, tm1', r), tm2'), Intro (Pi ((D, Maybe), V2)), L), ok2)
        end
        (* lam impossible *)
      | unifyExact (G, hastype (tm1, tm2), Vhs) =
        let
          (* Vh : L by invariant *)
          let (tm2', _ (* Uni L *), _ (* Uni (Next L) *)) = inferExact (G, tm2)
          let ((tm1', B, L), ok1) = unifyExact (G, tm1, Vhs)
        in
          ((hastype (tm1', tm2'), B, L), ok1)
        end
      | unifyExact (G, mismatch (tm1, tm2, location_msg, problem_msg), Vhs) =
        let
          let (tm1', _, L1) = inferExact (G, tm1)
          let ((tm2', B, L), ok2) = unifyExact (G, tm2, Vhs)
          let _ = delayMismatch (G, L1, L, termRegion tm2', location_msg, problem_msg)
        in
          ((mismatch (tm1', tm2', location_msg, problem_msg), B, L), ok2)
        end
      | unifyExact (G, omitapx (V (* = Vhs *), L, nL (* Next L *), r), Vhs) =
        let
          (* cannot raise Ambiguous *)
          let L' = Apx.apxToClass (G, L, nL, false)
          let V' = EClo Vhs
        in
          ((omitexact (V', L', r), Intro V', L'), true)
        end
      | unifyExact (G, tm, Vhs) =
        let
          let (tm', B', L') = inferExact (G, tm)
          let V' = toIntro (B', (L', id))
        in
          ((tm', B', L'), unifiableIdem (G, Vhs, (V', id)))
        end

    let rec occElim = function (constant (H, r), os, rs, i) -> 
        let
          (* should probably treat a constant with Foreign
             attribute as a redex *)
          let r' = List.foldr Paths.join r rs
        in
          (Paths.root (r', Paths.leaf r, conDecImp (headConDec H), i, os), r')
        end
      | (bvar (k, r), os, rs, i) -> 
        let
          let r' = List.foldr Paths.join r rs
        in
          (Paths.root (r', Paths.leaf r, 0, i, os), r')
        end
      | (fvar (name, r), os, rs, i) -> 
        let
          let r' = List.foldr Paths.join r rs
        in
          (Paths.root (r', Paths.leaf r, 0, i, os), r')
        end
      | (app (tm1, tm2), os, rs, i) -> 
        let
          let (oc2, r2) = occIntro tm2
        in
          occElim (tm1, Paths.app (oc2, os), r2::rs, i+1)
        end
      | (hastype (tm1, tm2), os, rs, i) -> occElim (tm1, os, rs, i)
      | (tm, os, rs, i) -> 
        (* this is some kind of redex or evar-under-substitution
           also catches simple introduction forms like `type' *)
        let
          let r' = List.foldr Paths.join (termRegion tm) rs
        in
          (Paths.leaf r', r')
        end

    and occIntro (arrow (tm1, tm2)) =
        let
          let (oc1, r1) = occIntro tm1
          let (oc2, r2) = occIntro tm2
          let r' = Paths.join (r1, r2)
        in
          (Paths.bind (r', SOME oc1, oc2), r')
        end
      | occIntro (pi (dec (name, tm1, r), tm2)) =
        let
          let (oc1, r1) = occIntro tm1
          let (oc2, r2) = occIntro tm2
          let r' = Paths.join (r, r2)
        in
          (* not quite consistent with older implementation for dec0 *)
          (Paths.bind (r', SOME oc1, oc2), r')
        end
      | occIntro (lam (dec (name, tm1, r), tm2)) =
        let
          let (oc1, r1) = occIntro tm1
          let (oc2, r2) = occIntro tm2
          let r' = Paths.join (r, r2)
        in
          (* not quite consistent with older implementation for dec0 *)
          (Paths.bind (r', SOME oc1, oc2), r')
        end
      | occIntro (hastype (tm1, tm2)) = occIntro tm1
      | occIntro (tm) =
        let
          (* still doesn't work quite right for the location -> occurrence map? *)
          let (oc, r) = occElim (tm, Paths.nils, nil, 0)
        in
          (oc, r)
        end

    let rec inferExactJob = function (G, jnothing) -> JNothing
      | (G, jand (j1, j2)) -> 
          JAnd (inferExactJob (G, j1), inferExactJob (G, j2))
      | (G, jwithctx (g, j)) -> 
        let
          let rec ie (Null) = (G, Null)
            | ie (Decl (g, tm)) =
              let
                let (G', Gresult) = ie (g)
                let (_, D) = inferExactDec (G', tm)
              in
                (Decl (G', D), Decl (Gresult, D))
              end
          let (G', Gresult) = ie (g)
        in
          JWithCtx (Gresult, inferExactJob (G', j))
        end
      | (G, jterm (tm)) -> 
        let
          let (tm', B, V) = inferExact (G, tm)
          let U = toIntro (B, (V, id))
          let (oc, r) = occIntro (tm')
          let rec iu (Uni Type) = Kind
            | iu (Pi (_, V)) = iu V
            | iu (Root _) = Type
            | iu (Redex (V, _)) = iu V
            | iu (Lam (_, V)) = iu V
            | iu (EClo (V, _)) = iu V
              (* others impossible *)
        in
          JTerm ((U, oc), V, iu V)
        end
      | (G, jclass (tm)) -> 
        let
          let (tm', B, L) = inferExact (G, tm)
          let V = toIntro (B, (L, id))
          let (oc, r) = occIntro (tm')
          let (Uni L, _) = Whnf.whnf (L, id)
        in
          JClass ((V, oc), L)
        end
      | (G, jof (tm1, tm2)) -> 
        let
          let (tm2', B2, L2) = inferExact (G, tm2)
          let V2 = toIntro (B2, (L2, id))
          let (tm1', B1) = checkExact (G, tm1, (V2, id),
                                       "Ascription in declaration did not hold\n"
                                       ^ "(Index object(s) did not match)")
          let U1 = toIntro (B1, (V2, id))
          let (oc2, r2) = occIntro tm2'
          let (oc1, r1) = occIntro tm1'
          let (Uni L2, _) = Whnf.whnf (L2, id)
        in
          JOf ((U1, oc1), (V2, oc2), L2)
        end

      | (G, jof' (tm1, V2)) -> 
        let
(*          let (tm2', B2, L2) = inferExact (G, tm2)
          let V2 = toIntro (B2, (L2, id)) *)
          let (tm1', B1) = checkExact (G, tm1, (V2, id),
                                       "Ascription in declaration did not hold\n"
                                       ^ "(Index object(s) did not match)")
          let U1 = toIntro (B1, (V2, id))
(*          let (oc2, r2) = occIntro tm2' *)
          let (oc1, r1) = occIntro tm1'
(*          let (Uni L2, _) = Whnf.whnf (L2, id) *)
        in
          JOf ((U1, oc1), (V2, oc1), Type)
        end

    let rec recon' (j) =
        let
          (* we leave it to the context to call Names.varReset
             reason: this code allows reconstructing terms containing
             existing EVars, and future developments might use that *)
          (* context must already have called resetErrors *)
          let _ = Apx.varReset ()
          let _ = varReset ()
          let j' = inferApxJob (Null, j)
          let _ = clearDelayed ()
          let j'' = inferExactJob (Null, j')
          let _ = runDelayed ()
          (* we leave it to the context to call checkErrors
             reason: the caller may want to do further processing on
             the "best effort" result returned, even if there were
             errors *)
        in
          j''
        end

    let rec recon (j) = (queryMode := false; recon' j)
    let rec reconQuery (j) = (queryMode := true; recon' j)

    (* Invariant, G must be named! *)
    let rec reconWithCtx' (G, j) =
        let
          (* we leave it to the context to call Names.varReset
             reason: this code allows reconstructing terms containing
             existing EVars, and future developments might use that *)
          (* context must already have called resetErrors *)
          let _ = Apx.varReset ()
          let _ = varReset ()
          let j' = inferApxJob' (G, j)
          let _ = clearDelayed ()
          let j'' = inferExactJob (G, j')
          let _ = runDelayed ()
          (* we leave it to the context to call checkErrors
             reason: the caller may want to do further processing on
             the "best effort" result returned, even if there were
             errors *)
        in
          j''
        end
    let rec reconWithCtx (G, j) = (queryMode := false; reconWithCtx' (G, j))
    let rec reconQueryWithCtx (G, j) = (queryMode := true; reconWithCtx' (G, j))

  let rec internalInst x = raise Match
  let rec externalInst x = raise Match

  end (* open IntSyn *)

end;; (* functor ReconTerm *)
