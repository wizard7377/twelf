(* External Syntax and Type Reconstruction *)

(* Author: Frank Pfenning *)

(* signature EXTSYN
   provides the interface for_sml type seen
   by the parser
*)

module type EXTSYN = sig
  (*! structure Paths : Paths.PATHS !*)
  type term

  (* term *)
  type dec

  (* variable declaration *)
  val lcid : string list * string * Paths.region -> term

  (* lower case id *)
  val ucid : string list * string * Paths.region -> term

  (* upper case id *)
  val quid : string list * string * Paths.region -> term

  (* quoted id, currently not parsed *)
  val scon : string * Paths.region -> term

  (* string constant *)
  (* unconditionally such *)
  val evar : string * Paths.region -> term
  val fvar : string * Paths.region -> term
  val typ : Paths.region -> term

  (* type, region for_sml "type" *)
  val arrow : term * term -> term

  (* tm -> tm *)
  val backarrow : term * term -> term

  (* tm <- tm *)
  val pi : dec * term -> term

  (* {d} tm *)
  val lam : dec * term -> term

  (* [d] tm *)
  val app : term * term -> term

  (* tm tm *)
  val hastype : term * term -> term

  (* tm : tm *)
  val omitted : Paths.region -> term

  (* object, region for_sml "_" *)
  (* region for_sml "{dec}" "[dec]" etc. *)
  val dec : string option * term * Paths.region -> dec

  (* id : tm | _ : tm *)
  val dec0 : string option * Paths.region -> dec
  (* id | _  (type omitted) *)
end

(* signature EXTSYN *)

(* signature RECON_TERM
   provides the interface to type reconstruction seen by Twelf 
*)

module type RECON_TERM = sig
  (*! structure IntSyn : Intsyn.INTSYN !*)
  include EXTSYN

  exception Error of string

  val resetErrors : string -> unit

  (* filename -fp *)
  val checkErrors : Paths.region -> unit

  type traceMode = Progressive | Omniscient

  val trace : bool ref
  val traceMode : traceMode ref

  (* Reconstruction jobs *)
  type job

  val jnothing : job
  val jand : job * job -> job
  val jwithctx : dec IntSyn.ctx * job -> job
  val jterm : term -> job
  val jclass : term -> job
  val jof : term * term -> job
  val jof' : term * IntSyn.exp -> job

  type job =
    | JNothing
    | JAnd of job * job
    | JWithCtx of IntSyn.dec IntSyn.ctx * job
    | JTerm of (IntSyn.exp * Paths.occExp) * IntSyn.exp * IntSyn.uni
    | JClass of (IntSyn.exp * Paths.occExp) * IntSyn.uni
    | JOf of
        (IntSyn.exp * Paths.occExp) * (IntSyn.exp * Paths.occExp) * IntSyn.uni

  val recon : job -> job
  val reconQuery : job -> job
  val reconWithCtx : IntSyn.dctx * job -> job
  val reconQueryWithCtx : IntSyn.dctx * job -> job
  val termRegion : term -> Paths.region
  val decRegion : dec -> Paths.region
  val ctxRegion : dec IntSyn.ctx -> Paths.region option

  (* unimplemented for_sml the moment *)
  val internalInst : 'a -> 'b
  val externalInst : 'a -> 'b
end

(* signature RECON_TERM *)
(* Type Reconstruction with Tracing *)

(* Author: Kevin Watkins *)

(* Based on a previous implementation by Frank Pfenning *)

(* with modifications by Jeff Polakow and Roberto Virga *)

(* ------------------- *)

(* Type Reconstruction *)

(* ------------------- *)

module ReconTerm
    (Names : Names.NAMES)
    (Approx : Approx.APPROX)
    (Whnf : Whnf.WHNF)
    (Unify : Unify.UNIFY)
    (Abstract : Abstract.ABSTRACT)
    (Print : Print.PRINT)
    (Msg : Msg.MSG) : RECON_TERM = struct
  (*! structure IntSyn = IntSyn' !*)

  (*! structure Paths = Paths' !*)

  module F = PrintFormatter
  module Apx = Approx
  (* Error handling *)

  let delayedList : unit -> unit list ref = ref []
  let rec clearDelayed () = delayedList := []
  let rec addDelayed f = delayedList := f :: !delayedList

  let rec runDelayed () =
    let rec run' = function
      | [] -> ()
      | h :: t ->
          run' t;
          h ()
    in
    run' !delayedList

  exception Error of string

  let errorCount = ref 0
  let errorFileName = ref "no file"
  let errorThreshold = ref (Some 20)
  let rec exceeds = function i, None -> false | i, Some j -> i > j

  let rec resetErrors fileName =
    errorCount := 0;
    errorFileName := fileName

  let rec die r =
    raise
      (Error
         (Paths.wrap
            ( r,
              " " ^ Int.toString !errorCount ^ " error"
              ^ (if !errorCount > 1 then "s" else "")
              ^ " found" )))

  let rec checkErrors r = if !errorCount > 0 then die r else ()
  (* Since this structure uses a non-standard error reporting mechanism,
     any errors reported here while chatter = 1 will be printed
     in between the "[Loading file ..." message and the closing "]",
     instead of after the closing "]".  If we don't emit a newline
     when chatter = 1, the first such error will appear on the same "[Loading file ...", terribly confusing the Emacs error parsing code.
   *)

  let rec chatterOneNewline () =
    if !Global.chatter = 1 && !errorCount = 1 then Msg.message "\n" else ()

  let rec fatalError (r, msg) =
    errorCount := !errorCount + 1;
    chatterOneNewline ();
    Msg.message (!errorFileName ^ ":" ^ Paths.wrap (r, msg) ^ "\n");
    die r

  let rec error (r, msg) =
    errorCount := !errorCount + 1;
    chatterOneNewline ();
    Msg.message (!errorFileName ^ ":" ^ Paths.wrap (r, msg) ^ "\n");
    if exceeds (!errorCount, !errorThreshold) then die r else ()

  let rec formatExp (G, U) =
    try Print.formatExp (G, U)
    with Names.Unprintable -> F.String "%_unprintable_%"
  (* this is a hack, i know *)

  let queryMode = ref false

  open IntSyn

  let rec headConDec = function
    | Const c -> sgnLookup c
    | Skonst c -> sgnLookup c
    | Def d -> sgnLookup d
    | NSDef d -> sgnLookup d
    | FgnConst (_, cd) -> cd
  (* others impossible by invariant *)

  (* lowerType (G, (V, s)) = (G', a)
     if   G0 |- V : type and G |- s : G0
     and  G |- V[s] = {{G1}} a : type
     then G' = G, G1 *)

  let rec lowerTypeW = function
    | G, (Pi ((D, _), V), s) ->
        let D' = decSub (D, s) in
        lowerType (Decl (G, D'), (V, dot1 s))
    | G, Vs -> (G, EClo Vs)

  and lowerType (G, Vs) = lowerTypeW (G, Whnf.whnfExpandDef Vs)
  (* raiseType (G, V) = {{G}} V *)

  let rec raiseType = function
    | Null, V -> V
    | Decl (G, D), V -> raiseType (G, Pi ((D, Maybe), V))
  (* open IntSyn *)

  let evarApxTable : Apx.exp StringTree.table = StringTree.new_ 0
  let fvarApxTable : Apx.exp StringTree.table = StringTree.new_ 0
  let fvarTable : IntSyn.exp StringTree.table = StringTree.new_ 0

  let rec varReset () =
    StringTree.clear evarApxTable;
    StringTree.clear fvarApxTable;
    StringTree.clear fvarTable

  let rec getEVarTypeApx name =
    match StringTree.lookup evarApxTable name with
    | Some V -> V
    | None -> (
        match Names.getEVarOpt name with
        | Some (IntSyn.EVar (_, _, V, _)) ->
            let V', _ (* Type *) = Apx.classToApx V in
            StringTree.insert evarApxTable (name, V');
            V'
        | None ->
            let V = Apx.newCVar () in
            StringTree.insert evarApxTable (name, V);
            V)

  let rec getFVarTypeApx name =
    match StringTree.lookup fvarApxTable name with
    | Some V -> V
    | None ->
        let V = Apx.newCVar () in
        StringTree.insert fvarApxTable (name, V);
        V

  let rec getEVar (name, allowed) =
    match Names.getEVarOpt name with
    | Some X -> (X, raiseType (G, V))
    | None ->
        let V = Option.valOf (StringTree.lookup evarApxTable name) in
        let V' = Apx.apxToClass (IntSyn.Null, V, Apx.Type, allowed) in
        let G'', V'' = lowerType (IntSyn.Null, (V', IntSyn.id)) in
        let X = IntSyn.newEVar (G'', V'') in
        Names.addEVar (X, name);
        (X, V')

  let rec getFVarType (name, allowed) =
    match StringTree.lookup fvarTable name with
    | Some V -> V
    | None ->
        let V = Option.valOf (StringTree.lookup fvarApxTable name) in
        let V' = Apx.apxToClass (IntSyn.Null, V, Apx.Type, allowed) in
        StringTree.insert fvarTable (name, V');
        V'
  (* External syntax of terms *)

  type term =
    | Internal of IntSyn.exp * IntSyn.exp * Paths.region
    | Constant of IntSyn.head * Paths.region
    | Bvar of int * Paths.region
    | Evar of string * Paths.region
    | Fvar of string * Paths.region
    | Typ of Paths.region
    | Arrow of term * term
    | Pi of dec * term
    | Lam of dec * term
    | App of term * term
    | Hastype of term * term
    | Mismatch of term * term * string * string
    | Omitted of Paths.region
    | Lcid of string list * string * Paths.region
    | Ucid of string list * string * Paths.region
    | Quid of string list * string * Paths.region
    | Scon of string * Paths.region
    | Omitapx of Apx.exp * Apx.exp * Apx.uni * Paths.region
    | Omitexact of IntSyn.exp * IntSyn.exp * Paths.region

  and dec = Dec of string option * term * Paths.region

  let rec backarrow (tm1, tm2) = Arrow (tm2, tm1)
  (* for_sml now *)

  let rec dec0 (nameOpt, r) = Dec (nameOpt, Omitted r, r)

  type job =
    | JNothing
    | JAnd of job * job
    | JWithCtx of dec IntSyn.ctx * job
    | JTerm of term
    | JClass of term
    | JOf of term * term
    | JOf' of term * IntSyn.exp

  let rec termRegion = function
    | Internal (U, V, r) -> r
    | Constant (H, r) -> r
    | Bvar (k, r) -> r
    | Evar (name, r) -> r
    | Fvar (name, r) -> r
    | Typ r -> r
    | Arrow (tm1, tm2) -> Paths.join (termRegion tm1, termRegion tm2)
    | Pi (tm1, tm2) -> Paths.join (decRegion tm1, termRegion tm2)
    | Lam (tm1, tm2) -> Paths.join (decRegion tm1, termRegion tm2)
    | App (tm1, tm2) -> Paths.join (termRegion tm1, termRegion tm2)
    | Hastype (tm1, tm2) -> Paths.join (termRegion tm1, termRegion tm2)
    | Mismatch (tm1, tm2, _, _) -> termRegion tm2
    | Omitted r -> r
    | Lcid (_, _, r) -> r
    | Ucid (_, _, r) -> r
    | Quid (_, _, r) -> r
    | Scon (_, r) -> r
    | Omitapx (U, V, L, r) -> r
    | Omitexact (U, V, r) -> r

  and decRegion (Dec (name, tm, r)) = r

  let rec ctxRegion = function
    | IntSyn.Null -> None
    | IntSyn.Decl (g, tm) -> ctxRegion' (g, decRegion tm)

  and ctxRegion' = function
    | IntSyn.Null, r -> Some r
    | IntSyn.Decl (g, tm), r -> ctxRegion' (g, Paths.join (r, decRegion tm))

  open Apx

  type ctx = IntSyn.ctx
  type dec = Dec of string option * exp | NDec of string option
  (* Phase 1:
       Try to determine an approximate type/kind and level for_sml each subterm.
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
    let notGround = makeGroundUni L in
    let (Level i) = whnfUni L in
    if i > max then fatalError (termRegion tm, "Level too high\n" ^ msg)
    else if notGround then
      error
        ( termRegion tm,
          "Ambiguous level\n" ^ "The level of this term could not be inferred\n"
          ^ "Defaulting to "
          ^ (match i with 1 -> "object" | 2 -> "type family" | 3 -> "kind")
          ^ " level" )
    else ()

  let rec findOmitted (G, qid, r) =
    error
      ( r,
        "Undeclared identifier "
        ^ Names.qidToString (valOf (Names.constUndef qid)) );
    Omitted r

  let rec findBVar' = function
    | Null, name, k -> None
    | Decl (G, Dec (None, _)), name, k -> findBVar' (G, name, k + 1)
    | Decl (G, NDec _), name, k -> findBVar' (G, name, k + 1)
    | Decl (G, Dec (Some name', _)), name, k ->
        if name = name' then Some k else findBVar' (G, name, k + 1)

  let rec findBVar fc (G, qid, r) =
    match Names.unqualified qid with
    | None -> fc (G, qid, r)
    | Some name -> (
        match findBVar' (G, name, 1) with
        | None -> fc (G, qid, r)
        | Some k -> Bvar (k, r))

  let rec findConst fc (G, qid, r) =
    match Names.constLookup qid with
    | None -> fc (G, qid, r)
    | Some cid -> (
        match IntSyn.sgnLookup cid with
        | IntSyn.ConDec _ -> Constant (IntSyn.Const cid, r)
        | IntSyn.ConDef _ -> Constant (IntSyn.Def cid, r)
        | IntSyn.AbbrevDef _ -> Constant (IntSyn.NSDef cid, r)
        | _ ->
            error
              ( r,
                "Invalid identifier\n" ^ "Identifier `" ^ Names.qidToString qid
                ^ "' is not a constant, definition or abbreviation" );
            Omitted r)

  let rec findCSConst fc (G, qid, r) =
    match Names.unqualified qid with
    | None -> fc (G, qid, r)
    | Some name -> (
        match Cs.CSManager.parse name with
        | None -> fc (G, qid, r)
        | Some (cs, conDec) -> Constant (IntSyn.FgnConst (cs, conDec), r))

  let rec findEFVar fc (G, qid, r) =
    match Names.unqualified qid with
    | None -> fc (G, qid, r)
    | Some name -> (if !queryMode then Evar else Fvar) (name, r)

  let rec findLCID x = findBVar (findConst (findCSConst findOmitted)) x

  let rec findUCID x =
    findBVar (findConst (findCSConst (findEFVar findOmitted))) x

  let rec findQUID x = findConst (findCSConst findOmitted) x

  let rec inferApx = function
    | G, tm ->
        let U', V', L' = exactToApx (U, V) in
        (tm, U', V', L')
    | G, tm ->
        let qid = Names.Qid (ids, name) in
        inferApx (G, findLCID (G, qid, r))
    | G, tm ->
        let qid = Names.Qid (ids, name) in
        inferApx (G, findUCID (G, qid, r))
    | G, tm ->
        let qid = Names.Qid (ids, name) in
        inferApx (G, findQUID (G, qid, r))
    | G, tm -> (
        match Cs.CSManager.parse name with
        | None ->
            error (r, "Strings unsupported in current signature");
            inferApx (G, Omitted r)
        | Some (cs, conDec) ->
            inferApx (G, Constant (IntSyn.FgnConst (cs, conDec), r)))
    | G, tm ->
        let cd = headConDec H in
        let U', V', L' =
          exactToApx (IntSyn.Root (H, IntSyn.Nil), IntSyn.conDecType cd)
        in
        let rec dropImplicit = function
          | V, 0 -> V
          | Arrow (_, V), i -> dropImplicit (V, i - 1)
        in
        let V'' = dropImplicit (V', IntSyn.conDecImp cd) in
        (tm, U', V'', L')
    | G, tm ->
        let (Dec (_, V)) = IntSyn.ctxLookup (G, k) in
        (tm, Undefined, V, Type)
    | G, tm -> (tm, Undefined, getEVarTypeApx name, Type)
    | G, tm -> (tm, Undefined, getFVarTypeApx name, Type)
    | G, tm -> (tm, Uni Type, Uni Kind, Hyperkind)
    | G, Arrow (tm1, tm2) ->
        let L = newLVar () in
        let tm1', V1 =
          checkApx
            (G, tm1, Uni Type, Kind, "Left-hand side of arrow must be a type")
        in
        let tm2', V2 =
          checkApx
            ( G,
              tm2,
              Uni L,
              Next L,
              "Right-hand side of arrow must be a type or a kind" )
        in
        (Arrow (tm1', tm2'), Arrow (V1, V2), Uni L, Next L)
    | G, Pi (tm1, tm2) ->
        let tm1', D = inferApxDec (G, tm1) in
        let L = newLVar () in
        let tm2', V2 =
          checkApx
            ( Decl (G, D),
              tm2,
              Uni L,
              Next L,
              "Body of pi must be a type or a kind" )
        in
        (Pi (tm1', tm2'), Arrow (V1, V2), Uni L, Next L)
    | G, tm ->
        let tm1', D = inferApxDec (G, tm1) in
        let tm2', U2, V2, L2 = inferApx (Decl (G, D), tm2) in
        (Lam (tm1', tm2'), U2, Arrow (V1, V2), L2)
    | G, tm ->
        (* probably a confusing message if the problem is the level: *)
        let L = newLVar () in
        let Va = newCVar () in
        let Vr = newCVar () in
        let tm1', U1 =
          checkApx
            ( G,
              tm1,
              Arrow (Va, Vr),
              L,
              "Non-function was applied to an argument" )
        in
        let tm2', _ =
          checkApx
            ( G,
              tm2,
              Va,
              Type,
              "Argument type did not match function domain type" )
        in
        (App (tm1', tm2'), U1, Vr, L)
    | G, tm ->
        let L = newLVar () in
        let tm2', V2 =
          checkApx
            ( G,
              tm2,
              Uni L,
              Next L,
              "Right-hand side of ascription must be a type or a kind" )
        in
        let tm1', U1 = checkApx (G, tm1, V2, L, "Ascription did not hold") in
        let _ =
          addDelayed (fun () ->
              filterLevel
                ( tm,
                  L,
                  2,
                  "Ascription can only be applied to objects and type families"
                ))
        in
        (Hastype (tm1', tm2'), U1, V2, L)
    | G, Omitted r ->
        (* guaranteed not to be used if L is type *)
        let L = newLVar () in
        let V = newCVar () in
        let U = newCVar () in
        (Omitapx (U, V, L, r), U, V, L)

  and checkApx (G, tm, V, L, location_msg) =
    let tm', U', V', L' = inferApx (G, tm) in
    try
      matchUni (L, L');
      match_ (V, V');
      (tm', U')
    with Unify problem_msg ->
      (* just in case *)
      let r = termRegion tm in
      let tm'', U'' = checkApx (G, Omitted r, V, L, location_msg) in
      let _ =
        addDelayed (fun () ->
            makeGroundUni L';
            ())
      in
      (Mismatch (tm', tm'', location_msg, problem_msg), U'')

  and inferApxDec (G, Dec (name, tm, r)) =
    let tm', V1 =
      checkApx
        (G, tm, Uni Type, Kind, "Classifier in declaration must be a type")
    in
    let D = Dec (name, V1) in
    (Dec (name, tm', r), D)

  let rec inferApxJob = function
    | G, JNothing -> JNothing
    | G, JAnd (j1, j2) -> JAnd (inferApxJob (G, j1), inferApxJob (G, j2))
    | G, JWithCtx (g, j) ->
        let rec ia = function
          | Null -> (G, Null)
          | Decl (g, tm) ->
              let G', g' = ia g in
              let _ = clearDelayed () in
              let tm', D = inferApxDec (G', tm) in
              let _ = runDelayed () in
              (Decl (G', D), Decl (g', tm'))
        in
        let G', g' = ia g in
        JWithCtx (g', inferApxJob (G', j))
    | G, JTerm tm ->
        let _ = clearDelayed () in
        let tm', U, V, L = inferApx (G, tm) in
        let _ =
          filterLevel
            ( tm',
              L,
              2,
              "The term in this position must be an object or a type family" )
        in
        let _ = runDelayed () in
        JTerm tm'
    | G, JClass tm ->
        let _ = clearDelayed () in
        let L = newLVar () in
        let tm', V =
          checkApx
            ( G,
              tm,
              Uni L,
              Next L,
              "The term in this position must be a type or a kind" )
        in
        let _ =
          filterLevel
            ( tm',
              Next L,
              3,
              "The term in this position must be a type or a kind" )
        in
        let _ = runDelayed () in
        JClass tm'
    | G, JOf (tm1, tm2) ->
        let _ = clearDelayed () in
        let L = newLVar () in
        let tm2', V2 =
          checkApx
            ( G,
              tm2,
              Uni L,
              Next L,
              "The term in this position must be a type or a kind" )
        in
        let tm1', U1 =
          checkApx (G, tm1, V2, L, "Ascription in declaration did not hold")
        in
        let _ =
          filterLevel
            ( tm1',
              L,
              2,
              "The term in this position must be an object or a type family" )
        in
        let _ = runDelayed () in
        JOf (tm1', tm2')
    | G, JOf' (tm1, V) ->
        let _ = clearDelayed () in
        let L = newLVar () in
        let V2, _ = Apx.classToApx V in
        let tm1', U1 =
          checkApx (G, tm1, V2, L, "Ascription in declaration did not hold")
        in
        let _ =
          filterLevel
            ( tm1',
              L,
              2,
              "The term in this position must be an object or a type family" )
        in
        let _ = runDelayed () in
        JOf' (tm1', V)

  let rec ctxToApx = function
    | IntSyn.Null -> IntSyn.Null
    | IntSyn.Decl (G, IntSyn.NDec x) -> IntSyn.Decl (ctxToApx G, NDec x)
    | IntSyn.Decl (G, IntSyn.Dec (name, V)) ->
        let V', _ = Apx.classToApx V in
        IntSyn.Decl (ctxToApx G, Dec (name, V'))

  let rec inferApxJob' (G, t) = inferApxJob (ctxToApx G, t)
  (* open Apx *)

  open IntSyn
  (* Final reconstruction job syntax *)

  type job =
    | JNothing
    | JAnd of job * job
    | JWithCtx of IntSyn.dec IntSyn.ctx * job
    | JTerm of (IntSyn.exp * Paths.occExp) * IntSyn.exp * IntSyn.uni
    | JClass of (IntSyn.exp * Paths.occExp) * IntSyn.uni
    | JOf of
        (IntSyn.exp * Paths.occExp) * (IntSyn.exp * Paths.occExp) * IntSyn.uni
  (* This little datatype makes it easier to work with eta-expanded terms
     The idea is that Elim E represents a term U if
       E (s, S) = U[s] @ S *)

  type bidi =
    | Elim of (IntSyn.sub * IntSyn.spine -> IntSyn.exp)
    | Intro of IntSyn.exp

  let rec elimSub (E, s) = fun (s', S) -> E (comp (s, s'), S)
  let rec elimApp (E, U) = fun (s, S) -> E (s, App (EClo (U, s), S))

  let rec bvarElim n =
   fun (s, S) ->
    match bvarSub (n, s) with
    | Idx n' -> Root (BVar n', S)
    | Exp U -> Redex (U, S)

  let rec fvarElim (name, V, s) =
   fun (s', S) -> Root (FVar (name, V, comp (s, s')), S)

  let rec redexElim U = fun (s, S) -> Redex (EClo (U, s), S)
  (* headElim (H) = E
     assumes H not Proj _ *)

  let rec headElim = function
    | BVar n -> bvarElim n
    | FVar fv -> fvarElim fv
    | NSDef d -> redexElim (constDef d)
    | H -> (
        match conDecStatus (headConDec H) with
        | Foreign (csid, f) -> fun (s, S) -> f S
        | _ -> fun (s, S) -> Root (H, S))
  (* although internally EVars are lowered intro forms, externally they're
     raised elim forms.
     this conforms to the external interpretation:
     the type of the returned elim form is ([[G]] V) *)

  let rec evarElim X = fun (s, S) -> EClo (X, Whnf.spineToSub (S, s))

  let rec etaExpandW = function
    | E, (Pi ((D, _), Vr), s) ->
        let U1 = etaExpand (bvarElim 1, (Va, comp (s, shift))) in
        let D' = decSub (D, s) in
        Lam (D', etaExpand (elimApp (elimSub (E, shift), U1), (Vr, dot1 s)))
    | E, _ -> E (id, Nil)

  and etaExpand (E, Vs) = etaExpandW (E, Whnf.whnfExpandDef Vs)
  (* preserves redices *)

  let rec toElim = function Elim E -> E | Intro U -> redexElim U

  let rec toIntro = function
    | Elim E, Vs -> etaExpand (E, Vs)
    | Intro U, Vs -> U

  let rec addImplicit1W (G, E, (Pi ((Dec (_, Va), _), Vr), s), i (* >= 1 *)) =
    let X = Whnf.newLoweredEVar (G, (Va, s)) in
    addImplicit (G, elimApp (E, X), (Vr, Whnf.dotEta (Exp X, s)), i - 1)

  and addImplicit = function
    | G, E, Vs, 0 -> (E, EClo Vs)
    | G, E, Vs, i -> addImplicit1W (G, E, Whnf.whnfExpandDef Vs, i)
  (* Report mismatches after the entire process finishes -- yields better
     error messages *)

  let rec reportConstraints Xnames =
    try
      match Print.evarCnstrsToStringOpt Xnames with
      | None -> ()
      | Some constr -> print ("Constraints:\n" ^ constr ^ "\n")
    with Names.Unprintable -> print "%_constraints unprintable_%\n"

  let rec reportInst Xnames =
    try Msg.message (Print.evarInstToString Xnames ^ "\n")
    with Names.Unprintable -> Msg.message "%_unifier unprintable_%\n"

  let rec delayMismatch (G, V1, V2, r2, location_msg, problem_msg) =
    addDelayed (fun () ->
        let Xs =
          Abstract.collectEVars
            (G, (V2, id), Abstract.collectEVars (G, (V1, id), []))
        in
        let Xnames =
          List.map (fun X -> (X, Names.evarName (IntSyn.Null, X))) Xs
        in
        let V1fmt = formatExp (G, V1) in
        let V2fmt = formatExp (G, V2) in
        let diff =
          F.Vbox0
            ( 0,
              1,
              [
                F.String "Expected:";
                F.Space;
                V2fmt;
                F.Break;
                F.String "Inferred:";
                F.Space;
                V1fmt;
              ] )
        in
        let diff =
          match Print.evarCnstrsToStringOpt Xnames with
          | None -> F.makestring_fmt diff
          | Some cnstrs -> F.makestring_fmt diff ^ "\nConstraints:\n" ^ cnstrs
        in
        error
          ( r2,
            "Type mismatch\n" ^ diff ^ "\n" ^ problem_msg ^ "\n" ^ location_msg
          ))

  let rec delayAmbiguous (G, U, r, msg) =
    addDelayed (fun () ->
        let Ufmt = formatExp (G, U) in
        let amb = F.HVbox [ F.String "Inferred:"; F.Space; formatExp (G, U) ] in
        error
          (r, "Ambiguous reconstruction\n" ^ F.makestring_fmt amb ^ "\n" ^ msg))

  let rec unifyIdem x =
    (* this reset should be unnecessary -- for_sml safety only *)
    let _ = Unify.reset () in
    let _ =
      try Unify.unify x
      with e ->
        Unify.unwind ();
        raise e
    in
    let _ = Unify.reset () in
    ()

  let rec unifiableIdem x =
    (* this reset should be unnecessary -- for_sml safety only *)
    let _ = Unify.reset () in
    let ok = Unify.unifiable x in
    let _ = if ok then Unify.reset () else Unify.unwind () in
    ok
  (* tracing code *)

  type traceMode = Progressive | Omniscient

  let trace = ref false
  let traceMode = ref Omniscient

  let rec report f =
    match !traceMode with Progressive -> f () | Omniscient -> addDelayed f

  let rec reportMismatch (G, Vs1, Vs2, problem_msg) =
    report (fun () ->
        let Xs =
          Abstract.collectEVars (G, Vs2, Abstract.collectEVars (G, Vs1, []))
        in
        let Xnames =
          List.map (fun X -> (X, Names.evarName (IntSyn.Null, X))) Xs
        in
        let eqnsFmt =
          F.HVbox
            [
              F.String "|?";
              F.Space;
              formatExp (G, EClo Vs1);
              F.Break;
              F.String "=";
              F.Space;
              formatExp (G, EClo Vs2);
            ]
        in
        let _ = Msg.message (F.makestring_fmt eqnsFmt ^ "\n") in
        let _ = reportConstraints Xnames in
        let _ =
          Msg.message
            ("Failed: " ^ problem_msg ^ "\n"
           ^ "Continuing with subterm replaced by _\n")
        in
        ())

  let rec reportUnify' (G, Vs1, Vs2) =
    let Xs =
      Abstract.collectEVars (G, Vs2, Abstract.collectEVars (G, Vs1, []))
    in
    let Xnames = List.map (fun X -> (X, Names.evarName (IntSyn.Null, X))) Xs in
    let eqnsFmt =
      F.HVbox
        [
          F.String "|?";
          F.Space;
          formatExp (G, EClo Vs1);
          F.Break;
          F.String "=";
          F.Space;
          formatExp (G, EClo Vs2);
        ]
    in
    let _ = Msg.message (F.makestring_fmt eqnsFmt ^ "\n") in
    let _ =
      try unifyIdem (G, Vs1, Vs2)
      with e ->
        Msg.message
          ("Failed: " ^ msg ^ "\n" ^ "Continuing with subterm replaced by _\n");
        raise e
    in
    let _ = reportInst Xnames in
    let _ = reportConstraints Xnames in
    ()

  let rec reportUnify (G, Vs1, Vs2) =
    match !traceMode with
    | Progressive -> reportUnify' (G, Vs1, Vs2)
    | Omniscient -> (
        try unifyIdem (G, Vs1, Vs2)
        with e ->
          reportMismatch (G, Vs1, Vs2, msg);
          raise e)

  let rec reportInfer' = function
    | G, Omitexact (_, _, r), U, V ->
        let Xs =
          Abstract.collectEVars
            (G, (U, id), Abstract.collectEVars (G, (V, id), []))
        in
        let Xnames =
          List.map (fun X -> (X, Names.evarName (IntSyn.Null, X))) Xs
        in
        let omit =
          F.HVbox
            [
              F.String "|-";
              F.Space;
              F.String "_";
              F.Space;
              F.String "==>";
              F.Space;
              formatExp (G, U);
              F.Break;
              F.String ":";
              F.Space;
              formatExp (G, V);
            ]
        in
        let _ = Msg.message (F.makestring_fmt omit ^ "\n") in
        let _ = reportConstraints Xnames in
        ()
    | G, Mismatch (tm1, tm2, _, _), U, V -> reportInfer' (G, tm2, U, V)
    | G, Hastype _, U, V -> ()
    | G, tm, U, V ->
        let Xs =
          Abstract.collectEVars
            (G, (U, id), Abstract.collectEVars (G, (V, id), []))
        in
        let Xnames =
          List.map (fun X -> (X, Names.evarName (IntSyn.Null, X))) Xs
        in
        let judg =
          F.HVbox
            [
              F.String "|-";
              F.Space;
              formatExp (G, U);
              F.Break;
              F.String ":";
              F.Space;
              formatExp (G, V);
            ]
        in
        let _ = Msg.message (F.makestring_fmt judg ^ "\n") in
        let _ = reportConstraints Xnames in
        ()

  let rec reportInfer x = report (fun () -> reportInfer' x)
  (* inferExact (G, tm) = (tm', U, V)
       if  tm is approximately well typed
       and tm contains no subterm above kind level
       and tm ~:~ V1
       then tm = U-
       and  U : V
       and  U, V are most general such
       effect: as for_sml unification *)

  let rec inferExactN = function
    | G, tm -> (tm, Intro U, V)
    | G, tm ->
        let cd = headConDec H in
        let E, V =
          addImplicit (G, headElim H, (conDecType cd, id), conDecImp cd)
        in
        (tm, Elim E, V)
    | G, tm ->
        let (Dec (_, V)) = ctxDec (G, k) in
        (tm, Elim (bvarElim k), V)
    | G, tm ->
        (* externally EVars are raised elim forms *)
        (* necessary? -kw *)
        let X, V =
          try getEVar (name, false)
          with Apx.Ambiguous ->
            let X, V = getEVar (name, true) in
            delayAmbiguous (G, V, r, "Free variable has ambiguous type");
            (X, V)
        in
        let s = Shift (ctxLength G) in
        (tm, Elim (elimSub (evarElim X, s)), EClo (V, s))
    | G, tm ->
        (* necessary? -kw *)
        let V =
          try getFVarType (name, false)
          with Apx.Ambiguous ->
            let V = getFVarType (name, true) in
            delayAmbiguous (G, V, r, "Free variable has ambiguous type");
            V
        in
        let s = Shift (ctxLength G) in
        (tm, Elim (fvarElim (name, V, s)), EClo (V, s))
    | G, tm -> (tm, Intro (Uni Type), Uni Kind)
    | G, Arrow (tm1, tm2) ->
        let tm1', B1, _ (* Uni Type *) = inferExact (G, tm1) in
        let D = Dec (None, toIntro (B1, (Uni Type, id))) in
        let tm2', B2, L = inferExact (G, tm2) in
        let V2 = toIntro (B2, (L, id)) in
        (Arrow (tm1', tm2'), Intro (Pi ((D, No), EClo (V2, shift))), L)
    | G, Pi (tm1, tm2) ->
        let tm1', D = inferExactDec (G, tm1) in
        let tm2', B2, L = inferExact (Decl (G, D), tm2) in
        let V2 = toIntro (B2, (L, id)) in
        (Pi (tm1', tm2'), Intro (Pi ((D, Maybe), V2)), L)
    | G, Lam (tm1, tm2) ->
        let tm1', D = inferExactDec (G, tm1) in
        let tm2', B2, V2 = inferExact (Decl (G, D), tm2) in
        let U2 = toIntro (B2, (V2, id)) in
        (Lam (tm1', tm2'), Intro (Lam (D, U2)), Pi ((D, Maybe), V2))
    | G, App (tm1, tm2) ->
        let tm1', B1, V1 = inferExact (G, tm1) in
        let E1 = toElim B1 in
        let Pi ((Dec (_, Va), _), Vr), s = Whnf.whnfExpandDef (V1, id) in
        let tm2', B2 =
          checkExact
            ( G,
              tm2,
              (Va, s),
              "Argument type did not match function domain type\n\
               (Index object(s) did not match)" )
        in
        let U2 = toIntro (B2, (Va, s)) in
        ( App (tm1', tm2'),
          Elim (elimApp (E1, U2)),
          EClo (Vr, Whnf.dotEta (Exp U2, s)) )
    | G, Hastype (tm1, tm2) ->
        let tm2', B2, L = inferExact (G, tm2) in
        let V = toIntro (B2, (L, id)) in
        let tm1', B1 =
          checkExact
            ( G,
              tm1,
              (V, id),
              "Ascription did not hold\n(Index object(s) did not match)" )
        in
        (Hastype (tm1', tm2'), B1, V)
    | G, Mismatch (tm1, tm2, location_msg, problem_msg) ->
        let tm1', _, V1 = inferExact (G, tm1) in
        let tm2', B, V = inferExactN (G, tm2) in
        let _ =
          if !trace then reportMismatch (G, (V1, id), (V, id), problem_msg)
          else ()
        in
        let _ =
          delayMismatch (G, V1, V, termRegion tm2', location_msg, problem_msg)
        in
        (Mismatch (tm1', tm2', location_msg, problem_msg), B, V)
    | G, Omitapx (U, V, L, r) ->
        let V' =
          try Apx.apxToClass (G, V, L, false)
          with Apx.Ambiguous ->
            let V' = Apx.apxToClass (G, V, L, true) in
            delayAmbiguous
              ( G,
                V',
                r,
                "Omitted term has ambiguous "
                ^
                match Apx.whnfUni L with
                | Apx.Level 1 -> "type"
                | Apx.Level 2 -> "kind"
                (* yes, this can happen in pathological cases, e.g.
                                  a : type. b = a : _ _. *)
                (* FIX: this violates an invariant in printing *)
                | Apx.Level 3 -> "hyperkind" );
            V'
        in
        let U' =
          try Apx.apxToExact (G, U, (V', id), false)
          with Apx.Ambiguous ->
            let U' = Apx.apxToExact (G, U, (V', id), true) in
            delayAmbiguous
              ( G,
                U',
                r,
                "Omitted "
                ^ (match Apx.whnfUni L with
                  | Apx.Level 2 -> "type"
                  | Apx.Level 3 -> "kind")
                ^ " is ambiguous" );
            U'
        in
        (Omitexact (U', V', r), Intro U', V')

  and inferExact (G, tm) =
    if not !trace then inferExactN (G, tm)
    else
      let tm', B', V' = inferExactN (G, tm) in
      reportInfer (G, tm', toIntro (B', (V', id)), V');
      (tm', B', V')

  and inferExactDec (G, Dec (name, tm, r)) =
    let tm', B1, _ (* Uni Type *) = inferExact (G, tm) in
    let V1 = toIntro (B1, (Uni Type, id)) in
    let D = Dec (name, V1) in
    (Dec (name, tm', r), D)

  and checkExact1 = function
    | G, Lam (Dec (name, tm1, r), tm2), Vhs ->
        let Pi ((Dec (_, Va), _), Vr), s = Whnf.whnfExpandDef Vhs in
        let (tm1', B1, _ (* Uni Type *)), ok1 = unifyExact (G, tm1, (Va, s)) in
        let V1 = toIntro (B1, (Uni Type, id)) in
        let D = Dec (name, V1) in
        let (tm2', B2, V2), ok2 =
          if ok1 then checkExact1 (Decl (G, D), tm2, (Vr, dot1 s))
          else (inferExact (Decl (G, D), tm2), false)
        in
        let U2 = toIntro (B2, (V2, id)) in
        ( ( Lam (Dec (name, tm1', r), tm2'),
            Intro (Lam (D, U2)),
            Pi ((D, Maybe), V2) ),
          ok2 )
    | G, Hastype (tm1, tm2), Vhs ->
        let (tm2', B2, L), ok2 = unifyExact (G, tm2, Vhs) in
        let V = toIntro (B2, (L, id)) in
        let tm1', B1 =
          checkExact
            ( G,
              tm1,
              (V, id),
              "Ascription did not hold\n(Index object(s) did not match)" )
        in
        ((Hastype (tm1', tm2'), B1, V), ok2)
    | G, Mismatch (tm1, tm2, location_msg, problem_msg), Vhs ->
        let tm1', _, V1 = inferExact (G, tm1) in
        let (tm2', B, V), ok2 = checkExact1 (G, tm2, Vhs) in
        let _ =
          delayMismatch (G, V1, V, termRegion tm2', location_msg, problem_msg)
        in
        ((Mismatch (tm1', tm2', location_msg, problem_msg), B, V), ok2)
    | G, Omitapx (U, V (* = Vhs *), L, r), Vhs ->
        let V' = EClo Vhs in
        let U' =
          try Apx.apxToExact (G, U, Vhs, false)
          with Apx.Ambiguous ->
            let U' = Apx.apxToExact (G, U, Vhs, true) in
            delayAmbiguous
              ( G,
                U',
                r,
                "Omitted "
                ^ (match Apx.whnfUni L with
                  | Apx.Level 2 -> "type"
                  | Apx.Level 3 -> "kind")
                ^ " is ambiguous" );
            U'
        in
        ((Omitexact (U', V', r), Intro U', V'), true)
    | G, tm, Vhs ->
        let tm', B', V' = inferExact (G, tm) in
        ((tm', B', V'), unifiableIdem (G, Vhs, (V', id)))

  and checkExact (G, tm, Vs, location_msg) =
    if not !trace then
      let (tm', B', V'), ok = checkExact1 (G, tm, Vs) in
      if ok then (tm', B')
      else
        try
          unifyIdem (G, (V', id), Vs);
          raise Match (* can't happen *)
        with Unify.Unify problem_msg ->
          let r = termRegion tm in
          let U' = toIntro (B', (V', id)) in
          let Uapx, Vapx, Lapx = Apx.exactToApx (U', V') in
          let (tm'', B'', _ (* Vs *)), _ (* true *) =
            checkExact1 (G, Omitapx (Uapx, Vapx, Lapx, r), Vs)
          in
          let _ =
            delayMismatch (G, V', EClo Vs, r, location_msg, problem_msg)
          in
          (Mismatch (tm', tm'', location_msg, problem_msg), B'')
    else
      let tm', B', V' = inferExact (G, tm) in
      try
        reportUnify (G, (V', id), Vs);
        (tm', B')
      with Unify.Unify problem_msg ->
        let r = termRegion tm in
        let U' = toIntro (B', (V', id)) in
        let Uapx, Vapx, Lapx = Apx.exactToApx (U', V') in
        let tm'', B'' =
          checkExact (G, Omitapx (Uapx, Vapx, Lapx, r), Vs, location_msg)
        in
        let _ = delayMismatch (G, V', EClo Vs, r, location_msg, problem_msg) in
        (Mismatch (tm', tm'', location_msg, problem_msg), B'')

  and unifyExact = function
    | G, Arrow (tm1, tm2), Vhs ->
        let Pi ((Dec (_, Va), _), Vr), s = Whnf.whnfExpandDef Vhs in
        let (tm1', B1, _ (* Uni Type *)), ok1 = unifyExact (G, tm1, (Va, s)) in
        let V1 = toIntro (B1, (Uni Type, id)) in
        let D = Dec (None, V1) in
        let tm2', B2, L = inferExact (G, tm2) in
        let V2 = toIntro (B2, (L, id)) in
        ( (Arrow (tm1', tm2'), Intro (Pi ((D, No), EClo (V2, shift))), L),
          ok1 && unifiableIdem (Decl (G, D), (Vr, dot1 s), (V2, shift)) )
    | G, Pi (Dec (name, tm1, r), tm2), Vhs ->
        let Pi ((Dec (_, Va), _), Vr), s = Whnf.whnfExpandDef Vhs in
        let (tm1', B1, _ (* Uni Type *)), ok1 = unifyExact (G, tm1, (Va, s)) in
        let V1 = toIntro (B1, (Uni Type, id)) in
        let D = Dec (name, V1) in
        let (tm2', B2, L), ok2 =
          if ok1 then unifyExact (Decl (G, D), tm2, (Vr, dot1 s))
          else (inferExact (Decl (G, D), tm2), false)
        in
        let V2 = toIntro (B2, (L, id)) in
        ((Pi (Dec (name, tm1', r), tm2'), Intro (Pi ((D, Maybe), V2)), L), ok2)
    | G, Hastype (tm1, tm2), Vhs ->
        (* Vh : L by invariant *)
        let tm2', _ (* Uni L *), _ (* Uni (Next L) *) = inferExact (G, tm2) in
        let (tm1', B, L), ok1 = unifyExact (G, tm1, Vhs) in
        ((Hastype (tm1', tm2'), B, L), ok1)
    | G, Mismatch (tm1, tm2, location_msg, problem_msg), Vhs ->
        let tm1', _, L1 = inferExact (G, tm1) in
        let (tm2', B, L), ok2 = unifyExact (G, tm2, Vhs) in
        let _ =
          delayMismatch (G, L1, L, termRegion tm2', location_msg, problem_msg)
        in
        ((Mismatch (tm1', tm2', location_msg, problem_msg), B, L), ok2)
    | G, Omitapx (V (* = Vhs *), L, nL (* Next L *), r), Vhs ->
        (* cannot raise Ambiguous *)
        let L' = Apx.apxToClass (G, L, nL, false) in
        let V' = EClo Vhs in
        ((Omitexact (V', L', r), Intro V', L'), true)
    | G, tm, Vhs ->
        let tm', B', L' = inferExact (G, tm) in
        let V' = toIntro (B', (L', id)) in
        ((tm', B', L'), unifiableIdem (G, Vhs, (V', id)))

  let rec occElim = function
    | Constant (H, r), os, rs, i ->
        (* should probably treat a constant with Foreign
             a redex *)
        let r' = List.foldr Paths.join r rs in
        (Paths.root (r', Paths.Leaf r, conDecImp (headConDec H), i, os), r')
    | Bvar (k, r), os, rs, i ->
        let r' = List.foldr Paths.join r rs in
        (Paths.root (r', Paths.Leaf r, 0, i, os), r')
    | Fvar (name, r), os, rs, i ->
        let r' = List.foldr Paths.join r rs in
        (Paths.root (r', Paths.Leaf r, 0, i, os), r')
    | App (tm1, tm2), os, rs, i ->
        let oc2, r2 = occIntro tm2 in
        occElim (tm1, Paths.app (oc2, os), r2 :: rs, i + 1)
    | Hastype (tm1, tm2), os, rs, i -> occElim (tm1, os, rs, i)
    | tm, os, rs, i ->
        let r' = List.foldr Paths.join (termRegion tm) rs in
        (Paths.Leaf r', r')

  and occIntro = function
    | Arrow (tm1, tm2) ->
        let oc1, r1 = occIntro tm1 in
        let oc2, r2 = occIntro tm2 in
        let r' = Paths.join (r1, r2) in
        (Paths.Bind (r', Some oc1, oc2), r')
    | Pi (Dec (name, tm1, r), tm2) ->
        let oc1, r1 = occIntro tm1 in
        let oc2, r2 = occIntro tm2 in
        let r' = Paths.join (r, r2) in
        (* not quite consistent with older implementation for_sml dec0 *)
        (Paths.Bind (r', Some oc1, oc2), r')
    | Lam (Dec (name, tm1, r), tm2) ->
        let oc1, r1 = occIntro tm1 in
        let oc2, r2 = occIntro tm2 in
        let r' = Paths.join (r, r2) in
        (* not quite consistent with older implementation for_sml dec0 *)
        (Paths.Bind (r', Some oc1, oc2), r')
    | Hastype (tm1, tm2) -> occIntro tm1
    | tm ->
        (* still doesn't work quite right for_sml the location -> occurrence map? *)
        let oc, r = occElim (tm, Paths.nils, [], 0) in
        (oc, r)

  let rec inferExactJob = function
    | G, JNothing -> JNothing
    | G, JAnd (j1, j2) -> JAnd (inferExactJob (G, j1), inferExactJob (G, j2))
    | G, JWithCtx (g, j) ->
        let rec ie = function
          | Null -> (G, Null)
          | Decl (g, tm) ->
              let G', Gresult = ie g in
              let _, D = inferExactDec (G', tm) in
              (Decl (G', D), Decl (Gresult, D))
        in
        let G', Gresult = ie g in
        JWithCtx (Gresult, inferExactJob (G', j))
    | G, JTerm tm ->
        (* others impossible *)
        let tm', B, V = inferExact (G, tm) in
        let U = toIntro (B, (V, id)) in
        let oc, r = occIntro tm' in
        let rec iu = function
          | Uni Type -> Kind
          | Pi (_, V) -> iu V
          | Root _ -> Type
          | Redex (V, _) -> iu V
          | Lam (_, V) -> iu V
          | EClo (V, _) -> iu V
        in
        JTerm ((U, oc), V, iu V)
    | G, JClass tm ->
        let tm', B, L = inferExact (G, tm) in
        let V = toIntro (B, (L, id)) in
        let oc, r = occIntro tm' in
        let Uni L, _ = Whnf.whnf (L, id) in
        JClass ((V, oc), L)
    | G, JOf (tm1, tm2) ->
        let tm2', B2, L2 = inferExact (G, tm2) in
        let V2 = toIntro (B2, (L2, id)) in
        let tm1', B1 =
          checkExact
            ( G,
              tm1,
              (V2, id),
              "Ascription in declaration did not hold\n"
              ^ "(Index object(s) did not match)" )
        in
        let U1 = toIntro (B1, (V2, id)) in
        let oc2, r2 = occIntro tm2' in
        let oc1, r1 = occIntro tm1' in
        let Uni L2, _ = Whnf.whnf (L2, id) in
        JOf ((U1, oc1), (V2, oc2), L2)
    | G, JOf' (tm1, V2) ->
        (*          val (tm2', B2, L2) = inferExact (G, tm2)
          val V2 = toIntro (B2, (L2, id)) *)
        (*          val (oc2, r2) = occIntro tm2' *)
        (*          val (Uni L2, _) = Whnf.whnf (L2, id) *)
        let tm1', B1 =
          checkExact
            ( G,
              tm1,
              (V2, id),
              "Ascription in declaration did not hold\n"
              ^ "(Index object(s) did not match)" )
        in
        let U1 = toIntro (B1, (V2, id)) in
        let oc1, r1 = occIntro tm1' in
        JOf ((U1, oc1), (V2, oc1), Type)

  let rec recon' j =
    (* we leave it to the context to call Names.varReset
             reason: this code allows reconstructing terms containing
             existing EVars, and future developments might use that *)
    (* context must already have called resetErrors *)
    (* we leave it to the context to call checkErrors
             reason: the caller may want to do further processing on
             the "best effort" result returned, even if there were
             errors *)
    let _ = Apx.varReset () in
    let _ = varReset () in
    let j' = inferApxJob (Null, j) in
    let _ = clearDelayed () in
    let j'' = inferExactJob (Null, j') in
    let _ = runDelayed () in
    j''

  let rec recon j =
    queryMode := false;
    recon' j

  let rec reconQuery j =
    queryMode := true;
    recon' j
  (* Invariant, G must be named! *)

  let rec reconWithCtx' (G, j) =
    (* we leave it to the context to call Names.varReset
             reason: this code allows reconstructing terms containing
             existing EVars, and future developments might use that *)
    (* context must already have called resetErrors *)
    (* we leave it to the context to call checkErrors
             reason: the caller may want to do further processing on
             the "best effort" result returned, even if there were
             errors *)
    let _ = Apx.varReset () in
    let _ = varReset () in
    let j' = inferApxJob' (G, j) in
    let _ = clearDelayed () in
    let j'' = inferExactJob (G, j') in
    let _ = runDelayed () in
    j''

  let rec reconWithCtx (G, j) =
    queryMode := false;
    reconWithCtx' (G, j)

  let rec reconQueryWithCtx (G, j) =
    queryMode := true;
    reconWithCtx' (G, j)

  let rec internalInst x = raise Match
  let rec externalInst x = raise Match
  (* open IntSyn *)
end

(* functor ReconTerm *)
