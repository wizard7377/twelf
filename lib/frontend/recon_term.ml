(* Type Reconstruction with Tracing *)
(* Author: Kevin Watkins *)
(* Based on a previous implementation by Frank Pfenning *)
(* with modifications by Jeff Polakow and Roberto Virga *)

(* ------------------- *)
(* Type Reconstruction *)
(* ------------------- *)

functor (* GEN BEGIN FUNCTOR DECL *) ReconTerm ((*! structure IntSyn' : INTSYN !*)
                   structure Names : NAMES
                   (*! sharing Names.IntSyn = IntSyn' !*)
                   (*! structure Paths' : PATHS !*)
                   structure Approx : APPROX
                   (*! sharing Approx.IntSyn = IntSyn' !*)
                   structure Whnf : WHNF
                   (*! sharing Whnf.IntSyn = IntSyn' !*)
                   structure Unify : UNIFY
                   (*! sharing Unify.IntSyn = IntSyn' !*)
                   structure Abstract : ABSTRACT
                   (*! sharing Abstract.IntSyn = IntSyn' !*)
                   structure Print : PRINT
                   (*! sharing Print.IntSyn = IntSyn' !*)
                   (*! structure CSManager : CS_MANAGER !*)
                   (*! sharing CSManager.IntSyn = IntSyn' !*)
                   structure StringTree : TABLE where type key = string
                   structure Msg : MSG)
  : RECON_TERM =
struct

  (*! structure IntSyn = IntSyn' !*)
  (*! structure Paths = Paths' !*)
  structure F = Print.Formatter
  structure Apx = Approx

  (* Error handling *)

  (* GEN BEGIN TAG OUTSIDE LET *) val delayedList : (unit -> unit) list ref = ref nil (* GEN END TAG OUTSIDE LET *)

  fun clearDelayed () = (delayedList := nil)
  fun addDelayed f = (delayedList := f::(!delayedList))
  fun runDelayed () =
      let
        fun (* GEN BEGIN FUN FIRST *) run' nil = () (* GEN END FUN FIRST *)
          | (* GEN BEGIN FUN BRANCH *) run' (h::t) = (run' t; h ()) (* GEN END FUN BRANCH *)
      in
        run' (!delayedList)
      end

  exception Error of string

  (* GEN BEGIN TAG OUTSIDE LET *) val errorCount = ref 0 (* GEN END TAG OUTSIDE LET *)
  (* GEN BEGIN TAG OUTSIDE LET *) val errorFileName = ref "no file" (* GEN END TAG OUTSIDE LET *)

  (* GEN BEGIN TAG OUTSIDE LET *) val errorThreshold = ref (SOME (20)) (* GEN END TAG OUTSIDE LET *)
  fun (* GEN BEGIN FUN FIRST *) exceeds (i, NONE) = false (* GEN END FUN FIRST *)
    | (* GEN BEGIN FUN BRANCH *) exceeds (i, SOME(j)) = i > j (* GEN END FUN BRANCH *)

  fun resetErrors (fileName) =
      (errorCount := 0;
       errorFileName := fileName)

  fun die (r) =
        raise Error (Paths.wrap (r,
                     " " ^ Int.toString (!errorCount)
                     ^ " error" ^ (if !errorCount > 1 then "s" else "")
                     ^ " found"))

  fun checkErrors (r) =
       if !errorCount > 0 then die (r) else ()

  (* Since this structure uses a non-standard error reporting mechanism,
     any errors reported here while chatter = 1 will be printed
     in between the "[Loading file ..." message and the closing "]",
     instead of after the closing "]".  If we don't emit a newline
     when chatter = 1, the first such error will appear on the same line
     as "[Loading file ...", terribly confusing the Emacs error parsing code.
   *)
  fun chatterOneNewline () =
      if !Global.chatter = 1 andalso !errorCount = 1
        then Msg.message "\n"
      else ()

  fun fatalError (r, msg) =
      (errorCount := !errorCount + 1;
       chatterOneNewline ();
       Msg.message (!errorFileName ^ ":" ^ Paths.wrap (r, msg) ^ "\n");
       die (r))

  fun error (r, msg) =
      (errorCount := !errorCount + 1;
       chatterOneNewline ();
       Msg.message (!errorFileName ^ ":" ^ Paths.wrap (r, msg) ^ "\n");
       if exceeds (!errorCount, !errorThreshold)
          then die (r)
       else ())

  fun formatExp (G, U) =
      Print.formatExp (G, U)
      handle Names.Unprintable => F.String "%_unprintable_%"

  (* this is a hack, i know *)
  (* GEN BEGIN TAG OUTSIDE LET *) val queryMode = ref false (* GEN END TAG OUTSIDE LET *)

  local
    open IntSyn
  in

  fun (* GEN BEGIN FUN FIRST *) headConDec (Const c) = sgnLookup c (* GEN END FUN FIRST *)
    | (* GEN BEGIN FUN BRANCH *) headConDec (Skonst c) = sgnLookup c (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) headConDec (Def d) = sgnLookup d (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) headConDec (NSDef d) = sgnLookup d (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) headConDec (FgnConst (_, cd)) = cd (* GEN END FUN BRANCH *)
      (* others impossible by invariant *)

  (* lowerType (G, (V, s)) = (G', a)
     if   G0 |- V : type and G |- s : G0
     and  G |- V[s] = {{G1}} a : type
     then G' = G, G1 *)
  fun (* GEN BEGIN FUN FIRST *) lowerTypeW (G, (Pi ((D, _), V), s)) =
      let
        (* GEN BEGIN TAG OUTSIDE LET *) val D' = decSub (D, s) (* GEN END TAG OUTSIDE LET *)
      in
        lowerType (Decl (G, D'), (V, dot1 s))
      end (* GEN END FUN FIRST *)
    | (* GEN BEGIN FUN BRANCH *) lowerTypeW (G, Vs) = (G, EClo Vs) (* GEN END FUN BRANCH *)
  and lowerType (G, Vs) = lowerTypeW (G, Whnf.whnfExpandDef Vs)

  (* raiseType (G, V) = {{G}} V *)
  fun (* GEN BEGIN FUN FIRST *) raiseType (Null, V) = V (* GEN END FUN FIRST *)
    | (* GEN BEGIN FUN BRANCH *) raiseType (Decl (G, D), V) = raiseType (G, Pi ((D, Maybe), V)) (* GEN END FUN BRANCH *)

  end (* open IntSyn *)

  local
    (* GEN BEGIN TAG OUTSIDE LET *) val evarApxTable : Apx.exp StringTree.table = StringTree.new (0) (* GEN END TAG OUTSIDE LET *)
    (* GEN BEGIN TAG OUTSIDE LET *) val fvarApxTable : Apx.exp StringTree.table = StringTree.new (0) (* GEN END TAG OUTSIDE LET *)

    (* GEN BEGIN TAG OUTSIDE LET *) val fvarTable : IntSyn.exp StringTree.table = StringTree.new (0) (* GEN END TAG OUTSIDE LET *)
  in

    fun varReset () = (StringTree.clear evarApxTable;
                       StringTree.clear fvarApxTable;
                       StringTree.clear fvarTable)

    fun getEVarTypeApx name =
        (case StringTree.lookup evarApxTable name
           of SOME V => V
            | NONE =>
        (case Names.getEVarOpt name
           of SOME (IntSyn.EVar (_, _, V, _)) =>
              let
                (* GEN BEGIN TAG OUTSIDE LET *) val (V', _ (* Type *)) = Apx.classToApx (V) (* GEN END TAG OUTSIDE LET *)
              in
                StringTree.insert evarApxTable (name, V');
                V'
              end
            | NONE =>
              let
                (* GEN BEGIN TAG OUTSIDE LET *) val V = Apx.newCVar () (* GEN END TAG OUTSIDE LET *)
              in
                StringTree.insert evarApxTable (name, V);
                V
              end))

    fun getFVarTypeApx name =
        (case StringTree.lookup fvarApxTable name
           of SOME V => V
            | NONE =>
              let
                (* GEN BEGIN TAG OUTSIDE LET *) val V = Apx.newCVar () (* GEN END TAG OUTSIDE LET *)
              in
                StringTree.insert fvarApxTable (name, V);
                V
              end)

    fun getEVar (name, allowed) =
        (case Names.getEVarOpt name
           of SOME (X as IntSyn.EVar (_, G, V, _)) => (X, raiseType (G, V))
            | NONE =>
              let
                (* GEN BEGIN TAG OUTSIDE LET *) val V = Option.valOf (StringTree.lookup evarApxTable name) (* GEN END TAG OUTSIDE LET *)
                (* GEN BEGIN TAG OUTSIDE LET *) val V' = Apx.apxToClass (IntSyn.Null, V, Apx.Type, allowed) (* GEN END TAG OUTSIDE LET *)
                (* GEN BEGIN TAG OUTSIDE LET *) val (G'', V'') = lowerType (IntSyn.Null, (V', IntSyn.id)) (* GEN END TAG OUTSIDE LET *)
                (* GEN BEGIN TAG OUTSIDE LET *) val X = IntSyn.newEVar (G'', V'') (* GEN END TAG OUTSIDE LET *)
              in
                Names.addEVar (X, name);
                (X, V')
              end)

    fun getFVarType (name, allowed) =
        (case StringTree.lookup fvarTable name
           of SOME V => V
            | NONE =>
              let
                (* GEN BEGIN TAG OUTSIDE LET *) val V = Option.valOf (StringTree.lookup fvarApxTable name) (* GEN END TAG OUTSIDE LET *)
                (* GEN BEGIN TAG OUTSIDE LET *) val V' = Apx.apxToClass (IntSyn.Null, V, Apx.Type, allowed) (* GEN END TAG OUTSIDE LET *)
              in
                StringTree.insert fvarTable (name, V');
                V'
              end)

  end

  (* External syntax of terms *)

  datatype term =
      internal of IntSyn.exp * IntSyn.exp * Paths.region (* (U, V, r) *)
        (* G |- U : V nf where V : L or V == kind *)
        (* not used currently *)

    | constant of IntSyn.head * Paths.region
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
    | omitapx of Apx.exp * Apx.exp * Apx.uni * Paths.region
        (* (U, V, L, r) where U ~:~ V ~:~ L *)
        (* U undefined unless L >= kind *)

      (* Phase 3 only *)
    | omitexact of IntSyn.exp * IntSyn.exp * Paths.region

  and dec =
      dec of string option * term * Paths.region

  fun backarrow (tm1, tm2) = arrow (tm2, tm1)

  (* for now *)
  fun dec0 (nameOpt, r) = dec (nameOpt, omitted (r), r)

  datatype job =
      jnothing
    | jand of job * job
    | jwithctx of dec IntSyn.ctx * job
    | jterm of term
    | jclass of term
    | jof of term * term
    | jof' of term * IntSyn.exp

  fun (* GEN BEGIN FUN FIRST *) termRegion (internal (U, V, r)) = r (* GEN END FUN FIRST *)
    | (* GEN BEGIN FUN BRANCH *) termRegion (constant (H, r)) = r (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) termRegion (bvar (k, r)) = r (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) termRegion (evar (name, r)) = r (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) termRegion (fvar (name, r)) = r (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) termRegion (typ (r)) = r (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) termRegion (arrow (tm1, tm2)) =
        Paths.join (termRegion tm1, termRegion tm2) (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) termRegion (pi (tm1, tm2)) =
        Paths.join (decRegion tm1, termRegion tm2) (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) termRegion (lam (tm1, tm2)) =
        Paths.join (decRegion tm1, termRegion tm2) (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) termRegion (app (tm1, tm2)) =
        Paths.join (termRegion tm1, termRegion tm2) (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) termRegion (hastype (tm1, tm2)) =
        Paths.join (termRegion tm1, termRegion tm2) (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) termRegion (mismatch (tm1, tm2, _, _)) =
        termRegion tm2 (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) termRegion (omitted (r)) = r (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) termRegion (lcid (_, _, r)) = r (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) termRegion (ucid (_, _, r)) = r (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) termRegion (quid (_, _, r)) = r (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) termRegion (scon (_, r)) = r (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) termRegion (omitapx (U, V, L, r)) = r (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) termRegion (omitexact (U, V, r)) = r (* GEN END FUN BRANCH *)

  and decRegion (dec (name, tm, r)) = r

  fun (* GEN BEGIN FUN FIRST *) ctxRegion (IntSyn.Null) = NONE (* GEN END FUN FIRST *)
    | (* GEN BEGIN FUN BRANCH *) ctxRegion (IntSyn.Decl (g, tm)) =
        ctxRegion' (g, decRegion tm) (* GEN END FUN BRANCH *)

  and (* GEN BEGIN FUN FIRST *) ctxRegion' (IntSyn.Null, r) = SOME r (* GEN END FUN FIRST *)
    | (* GEN BEGIN FUN BRANCH *) ctxRegion' (IntSyn.Decl (g, tm), r) =
        ctxRegion' (g, Paths.join (r, decRegion tm)) (* GEN END FUN BRANCH *)

  local
    open Apx
    datatype ctx = datatype IntSyn.ctx
    datatype dec = Dec of string option * exp | NDec of string option
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

    fun filterLevel (tm, L, max, msg) =
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val notGround = makeGroundUni L (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val Level i = whnfUni L (* GEN END TAG OUTSIDE LET *)
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

    fun findOmitted (G, qid, r) =
          (error (r, "Undeclared identifier "
                     ^ Names.qidToString (valOf (Names.constUndef qid)));
           omitted (r))

    fun (* GEN BEGIN FUN FIRST *) findBVar' (Null, name, k) = NONE (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) findBVar' (Decl (G, Dec (NONE, _)), name, k) =
          findBVar' (G, name, k+1) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) findBVar' (Decl (G, NDec _), name, k) =
          findBVar' (G, name, k+1) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) findBVar' (Decl (G, Dec (SOME(name'), _)), name, k) =
          if name = name' then SOME (k)
          else findBVar' (G, name, k+1) (* GEN END FUN BRANCH *)

    fun findBVar fc (G, qid, r) =
        (case Names.unqualified qid
           of NONE => fc (G, qid, r)
            | SOME name =>
              (case findBVar' (G, name, 1)
                 of NONE => fc (G, qid, r)
                  | SOME k => bvar (k, r)))

    fun findConst fc (G, qid, r) =
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

    fun findCSConst fc (G, qid, r) =
        (case Names.unqualified qid
           of NONE => fc (G, qid, r)
            | SOME name =>
              (case CSManager.parse name
                 of NONE => fc (G, qid, r)
                  | SOME (cs, conDec) =>
                      constant (IntSyn.FgnConst (cs, conDec), r)))

    fun findEFVar fc (G, qid, r) =
        (case Names.unqualified qid
           of NONE => fc (G, qid, r)
            | SOME name => (if !queryMode then evar else fvar) (name, r))

    fun findLCID x = findBVar (findConst (findCSConst findOmitted)) x
    fun findUCID x = findBVar (findConst (findCSConst (findEFVar findOmitted))) x
    fun findQUID x = findConst (findCSConst findOmitted) x


    fun (* GEN BEGIN FUN FIRST *) inferApx (G, tm as internal (U, V, r)) =
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val (U', V', L') = exactToApx (U, V) (* GEN END TAG OUTSIDE LET *)
        in
          (tm, U', V', L')
        end (* GEN END FUN FIRST *)

      | (* GEN BEGIN FUN BRANCH *) inferApx (G, tm as lcid (ids, name, r)) =
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val qid = Names.Qid (ids, name) (* GEN END TAG OUTSIDE LET *)
        in
          inferApx (G, findLCID (G, qid, r))
        end (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) inferApx (G, tm as ucid (ids, name, r)) =
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val qid = Names.Qid (ids, name) (* GEN END TAG OUTSIDE LET *)
        in
          inferApx (G, findUCID (G, qid, r))
        end (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) inferApx (G, tm as quid (ids, name, r)) =
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val qid = Names.Qid (ids, name) (* GEN END TAG OUTSIDE LET *)
        in
          inferApx (G, findQUID (G, qid, r))
        end (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) inferApx (G, tm as scon (name, r)) =
          (case CSManager.parse name
             of NONE => (error (r, "Strings unsupported in current signature");
                         inferApx (G, omitted (r)))
              | SOME (cs, conDec) =>
                  inferApx (G, constant (IntSyn.FgnConst (cs, conDec), r))) (* GEN END FUN BRANCH *)

      | (* GEN BEGIN FUN BRANCH *) inferApx (G, tm as constant (H, r)) =
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val cd = headConDec H (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val (U', V', L') = exactToApx (IntSyn.Root (H, IntSyn.Nil),
                                         IntSyn.conDecType cd) (* GEN END TAG OUTSIDE LET *)
          fun (* GEN BEGIN FUN FIRST *) dropImplicit (V, 0) = V (* GEN END FUN FIRST *)
            | (* GEN BEGIN FUN BRANCH *) dropImplicit (Arrow (_, V), i) = dropImplicit (V, i-1) (* GEN END FUN BRANCH *)
          (* GEN BEGIN TAG OUTSIDE LET *) val V'' = dropImplicit (V', IntSyn.conDecImp cd) (* GEN END TAG OUTSIDE LET *)
        in
          (tm, U', V'', L')
        end (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) inferApx (G, tm as bvar (k, r)) =
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val Dec (_, V) = IntSyn.ctxLookup (G, k) (* GEN END TAG OUTSIDE LET *)
        in
          (tm, Undefined, V, Type)
        end (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) inferApx (G, tm as evar (name, r)) =
          (tm, Undefined, getEVarTypeApx name, Type) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) inferApx (G, tm as fvar (name, r)) =
          (tm, Undefined, getFVarTypeApx name, Type) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) inferApx (G, tm as typ (r)) =
          (tm, Uni Type, Uni Kind, Hyperkind) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) inferApx (G, arrow (tm1, tm2)) =
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val L = newLVar () (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val (tm1', V1) = checkApx (G, tm1, Uni Type, Kind,
                                     "Left-hand side of arrow must be a type") (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val (tm2', V2) = checkApx (G, tm2, Uni L, Next L,
                                     "Right-hand side of arrow must be a type or a kind") (* GEN END TAG OUTSIDE LET *)
        in
          (arrow (tm1', tm2'), Arrow (V1, V2), Uni L, Next L)
        end (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) inferApx (G, pi (tm1, tm2)) =
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val (tm1', D as Dec (_, V1)) = inferApxDec (G, tm1) (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val L = newLVar () (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val (tm2', V2) = checkApx (Decl (G, D), tm2, Uni L, Next L,
                                     "Body of pi must be a type or a kind") (* GEN END TAG OUTSIDE LET *)
        in
          (pi (tm1', tm2'), Arrow (V1, V2), Uni L, Next L)
        end (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) inferApx (G, tm as lam (tm1, tm2)) =
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val (tm1', D as Dec (_, V1)) = inferApxDec (G, tm1) (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val (tm2', U2, V2, L2) = inferApx (Decl (G, D), tm2) (* GEN END TAG OUTSIDE LET *)
        in
          (lam (tm1', tm2'), U2, Arrow (V1, V2), L2)
        end (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) inferApx (G, tm as app (tm1, tm2)) =
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val L = newLVar () (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val Va = newCVar () (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val Vr = newCVar () (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val (tm1', U1) = checkApx (G, tm1, Arrow (Va, Vr), L,
                                     "Non-function was applied to an argument") (* GEN END TAG OUTSIDE LET *)
          (* probably a confusing message if the problem is the level: *)
          (* GEN BEGIN TAG OUTSIDE LET *) val (tm2', _) = checkApx (G, tm2, Va, Type,
                                    "Argument type did not match function domain type") (* GEN END TAG OUTSIDE LET *)
        in
          (app (tm1', tm2'), U1, Vr, L)
        end (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) inferApx (G, tm as hastype (tm1, tm2)) =
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val L = newLVar () (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val (tm2', V2) = checkApx (G, tm2, Uni L, Next L,
                                     "Right-hand side of ascription must be a type or a kind") (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val (tm1', U1) = checkApx (G, tm1, V2, L,
                                     "Ascription did not hold") (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val _ = addDelayed ((* GEN BEGIN FUNCTION EXPRESSION *) fn () => filterLevel (tm, L, 2, "Ascription can only be applied to objects and type families") (* GEN END FUNCTION EXPRESSION *)) (* GEN END TAG OUTSIDE LET *)
        in
          (hastype (tm1', tm2'), U1, V2, L)
        end (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) inferApx (G, omitted (r)) =
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val L = newLVar () (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val V = newCVar () (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val U = newCVar () (* GEN END TAG OUTSIDE LET *) (* guaranteed not to be used if L is type *)
        in
          (omitapx (U, V, L, r), U, V, L)
        end (* GEN END FUN BRANCH *)

    and checkApx (G, tm, V, L, location_msg) =
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val (tm', U', V', L') = inferApx (G, tm) (* GEN END TAG OUTSIDE LET *)
        in
          (matchUni (L, L'); match (V, V'); (tm', U'))
          handle Unify problem_msg =>
          let
            (* GEN BEGIN TAG OUTSIDE LET *) val r = termRegion tm (* GEN END TAG OUTSIDE LET *)
            (* GEN BEGIN TAG OUTSIDE LET *) val (tm'', U'') = checkApx (G, omitted (r), V, L, location_msg) (* GEN END TAG OUTSIDE LET *)
            (* just in case *)
            (* GEN BEGIN TAG OUTSIDE LET *) val _ = addDelayed ((* GEN BEGIN FUNCTION EXPRESSION *) fn () => (makeGroundUni L'; ()) (* GEN END FUNCTION EXPRESSION *)) (* GEN END TAG OUTSIDE LET *)
          in
            (mismatch (tm', tm'', location_msg, problem_msg), U'')
          end
        end

    and inferApxDec (G, dec (name, tm, r)) =
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val (tm', V1) = checkApx (G, tm, Uni Type, Kind,
                                    "Classifier in declaration must be a type") (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val D = Dec (name, V1) (* GEN END TAG OUTSIDE LET *)
        in
          (dec (name, tm', r), D)
        end

    fun (* GEN BEGIN FUN FIRST *) inferApxJob (G, jnothing) = jnothing (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) inferApxJob (G, jand (j1, j2)) =
          jand (inferApxJob (G, j1), inferApxJob (G, j2)) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) inferApxJob (G, jwithctx (g, j)) =
        let
          fun (* GEN BEGIN FUN FIRST *) ia (Null) = (G, Null) (* GEN END FUN FIRST *)
            | (* GEN BEGIN FUN BRANCH *) ia (Decl (g, tm)) =
              let
                (* GEN BEGIN TAG OUTSIDE LET *) val (G', g') = ia (g) (* GEN END TAG OUTSIDE LET *)
                (* GEN BEGIN TAG OUTSIDE LET *) val _ = clearDelayed () (* GEN END TAG OUTSIDE LET *)
                (* GEN BEGIN TAG OUTSIDE LET *) val (tm', D) = inferApxDec (G', tm) (* GEN END TAG OUTSIDE LET *)
                (* GEN BEGIN TAG OUTSIDE LET *) val _ = runDelayed () (* GEN END TAG OUTSIDE LET *)
              in
                (Decl (G', D), Decl (g', tm'))
              end (* GEN END FUN BRANCH *)
          (* GEN BEGIN TAG OUTSIDE LET *) val (G', g') = ia (g) (* GEN END TAG OUTSIDE LET *)
        in
          jwithctx (g', inferApxJob (G', j))
        end (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) inferApxJob (G, jterm (tm)) =
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val _ = clearDelayed () (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val (tm', U, V, L) = inferApx (G, tm) (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val _ = filterLevel (tm', L, 2,
                               "The term in this position must be an object or a type family") (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val _ = runDelayed () (* GEN END TAG OUTSIDE LET *)
        in
          jterm (tm')
        end (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) inferApxJob (G, jclass (tm)) =
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val _ = clearDelayed () (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val L = newLVar () (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val (tm', V) = checkApx (G, tm, Uni L, Next L,
                                   "The term in this position must be a type or a kind") (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val _ = filterLevel (tm', Next L, 3,
                               "The term in this position must be a type or a kind") (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val _ = runDelayed () (* GEN END TAG OUTSIDE LET *)
        in
          jclass (tm')
        end (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) inferApxJob (G, jof (tm1, tm2)) =
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val _ = clearDelayed () (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val L = newLVar () (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val (tm2', V2) = checkApx (G, tm2, Uni L, Next L,
                                     "The term in this position must be a type or a kind") (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val (tm1', U1) = checkApx (G, tm1, V2, L,
                                     "Ascription in declaration did not hold") (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val _ = filterLevel (tm1', L, 2,
                               "The term in this position must be an object or a type family") (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val _ = runDelayed () (* GEN END TAG OUTSIDE LET *)
        in
          jof (tm1', tm2')
        end (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) inferApxJob (G, jof' (tm1, V)) =
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val _ = clearDelayed () (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val L = newLVar () (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val (V2, _) = Apx.classToApx V (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val (tm1', U1) = checkApx (G, tm1, V2, L,
                                     "Ascription in declaration did not hold") (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val _ = filterLevel (tm1', L, 2,
                               "The term in this position must be an object or a type family") (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val _ = runDelayed () (* GEN END TAG OUTSIDE LET *)
        in
          jof' (tm1', V)
        end (* GEN END FUN BRANCH *)

    fun (* GEN BEGIN FUN FIRST *) ctxToApx IntSyn.Null = IntSyn.Null (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) ctxToApx (IntSyn.Decl (G, IntSyn.NDec x)) =
          IntSyn.Decl (ctxToApx G, NDec x) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) ctxToApx (IntSyn.Decl (G, IntSyn.Dec (name, V))) =
          let
            (* GEN BEGIN TAG OUTSIDE LET *) val (V', _) = Apx.classToApx V (* GEN END TAG OUTSIDE LET *)
          in
            IntSyn.Decl (ctxToApx G, Dec (name, V'))
          end (* GEN END FUN BRANCH *)

    fun inferApxJob' (G, t) =
        inferApxJob (ctxToApx G, t)

  end (* open Apx *)

  local
    open IntSyn
  in

  (* Final reconstruction job syntax *)

  datatype job =
      JNothing
    | JAnd of job * job
    | JWithCtx of IntSyn.dec IntSyn.ctx * job
    | JTerm of (IntSyn.exp * Paths.occ_exp) * IntSyn.exp * IntSyn.uni
    | JClass of (IntSyn.exp * Paths.occ_exp) * IntSyn.uni
    | JOf of (IntSyn.exp * Paths.occ_exp) * (IntSyn.exp * Paths.occ_exp) * IntSyn.uni

  (* This little datatype makes it easier to work with eta-expanded terms
     The idea is that Elim E represents a term U if
       E (s, S) = U[s] @ S *)

  datatype bidi =
      Elim of IntSyn.sub * IntSyn.spine -> IntSyn.exp
    | Intro of IntSyn.exp

  fun elimSub (E, s) = ((* GEN BEGIN FUNCTION EXPRESSION *) fn (s', S) => E (comp (s, s'), S) (* GEN END FUNCTION EXPRESSION *))
  fun elimApp (E, U) = ((* GEN BEGIN FUNCTION EXPRESSION *) fn (s, S) => E (s, App (EClo (U, s), S)) (* GEN END FUNCTION EXPRESSION *))

  fun bvarElim (n) = ((* GEN BEGIN FUNCTION EXPRESSION *) fn (s, S) =>
      (case bvarSub (n, s)
         of Idx (n') => Root (BVar n', S)
          | Exp (U) => Redex (U, S)) (* GEN END FUNCTION EXPRESSION *))
  fun fvarElim (name, V, s) =
        ((* GEN BEGIN FUNCTION EXPRESSION *) fn (s', S) => Root (FVar (name, V, comp (s, s')), S) (* GEN END FUNCTION EXPRESSION *))
  fun redexElim (U) = ((* GEN BEGIN FUNCTION EXPRESSION *) fn (s, S) => Redex (EClo (U, s), S) (* GEN END FUNCTION EXPRESSION *))
  (* headElim (H) = E
     assumes H not Proj _ *)
  fun (* GEN BEGIN FUN FIRST *) headElim (BVar n) = bvarElim n (* GEN END FUN FIRST *)
    | (* GEN BEGIN FUN BRANCH *) headElim (FVar fv) = fvarElim fv (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) headElim (NSDef d) = redexElim (constDef d) (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) headElim (H) =
      (case conDecStatus (headConDec H)
         of Foreign (csid, f) => ((* GEN BEGIN FUNCTION EXPRESSION *) fn (s, S) => f S (* GEN END FUNCTION EXPRESSION *))
          | _ => ((* GEN BEGIN FUNCTION EXPRESSION *) fn (s, S) => Root (H, S) (* GEN END FUNCTION EXPRESSION *))) (* GEN END FUN BRANCH *)
  (* although internally EVars are lowered intro forms, externally they're
     raised elim forms.
     this conforms to the external interpretation:
     the type of the returned elim form is ([[G]] V) *)
  fun evarElim (X as EVar _) =
        ((* GEN BEGIN FUNCTION EXPRESSION *) fn (s, S) => EClo (X, Whnf.spineToSub (S, s)) (* GEN END FUNCTION EXPRESSION *))

  fun (* GEN BEGIN FUN FIRST *) etaExpandW (E, (Pi ((D as Dec (_, Va), _), Vr), s)) =
      let
        (* GEN BEGIN TAG OUTSIDE LET *) val U1 = etaExpand (bvarElim (1), (Va, comp (s, shift))) (* GEN END TAG OUTSIDE LET *)
        (* GEN BEGIN TAG OUTSIDE LET *) val D' = decSub (D, s) (* GEN END TAG OUTSIDE LET *)
      in
        Lam (D', etaExpand (elimApp (elimSub (E, shift), U1), (Vr, dot1 s)))
      end (* GEN END FUN FIRST *)
    | (* GEN BEGIN FUN BRANCH *) etaExpandW (E, _) = E (id, Nil) (* GEN END FUN BRANCH *)
  and etaExpand (E, Vs) = etaExpandW (E, Whnf.whnfExpandDef Vs)

  (* preserves redices *)
  fun (* GEN BEGIN FUN FIRST *) toElim (Elim E) = E (* GEN END FUN FIRST *)
    | (* GEN BEGIN FUN BRANCH *) toElim (Intro U) = redexElim U (* GEN END FUN BRANCH *)

  fun (* GEN BEGIN FUN FIRST *) toIntro (Elim E, Vs) = etaExpand (E, Vs) (* GEN END FUN FIRST *)
    | (* GEN BEGIN FUN BRANCH *) toIntro (Intro U, Vs) = U (* GEN END FUN BRANCH *)

  fun addImplicit1W (G, E, (Pi ((Dec (_, Va), _), Vr), s), i (* >= 1 *)) =
      let
        (* GEN BEGIN TAG OUTSIDE LET *) val X = Whnf.newLoweredEVar (G, (Va, s)) (* GEN END TAG OUTSIDE LET *)
      in
        addImplicit (G, elimApp (E, X), (Vr, Whnf.dotEta (Exp (X), s)), i-1)
      end

      (* if no implicit arguments, do not expand Vs!!! *)
  and (* GEN BEGIN FUN FIRST *) addImplicit (G, E, Vs, 0) = (E, EClo Vs) (* GEN END FUN FIRST *)
    | (* GEN BEGIN FUN BRANCH *) addImplicit (G, E, Vs, i) = addImplicit1W (G, E, Whnf.whnfExpandDef Vs, i) (* GEN END FUN BRANCH *)


  (* Report mismatches after the entire process finishes -- yields better
     error messages *)

  fun reportConstraints (Xnames) =
      (case Print.evarCnstrsToStringOpt (Xnames)
         of NONE => ()
          | SOME(constr) => print ("Constraints:\n" ^ constr ^ "\n"))
      handle Names.Unprintable => print "%_constraints unprintable_%\n"

  fun reportInst (Xnames) =
      (Msg.message (Print.evarInstToString (Xnames) ^ "\n"))
      handle Names.Unprintable => Msg.message "%_unifier unprintable_%\n"

  fun delayMismatch (G, V1, V2, r2, location_msg, problem_msg) =
      addDelayed ((* GEN BEGIN FUNCTION EXPRESSION *) fn () =>
      let
        (* GEN BEGIN TAG OUTSIDE LET *) val Xs = Abstract.collectEVars (G, (V2, id),
                 Abstract.collectEVars (G, (V1, id), nil)) (* GEN END TAG OUTSIDE LET *)
        (* GEN BEGIN TAG OUTSIDE LET *) val Xnames = List.map ((* GEN BEGIN FUNCTION EXPRESSION *) fn X => (X, Names.evarName (IntSyn.Null, X)) (* GEN END FUNCTION EXPRESSION *)) Xs (* GEN END TAG OUTSIDE LET *)
        (* GEN BEGIN TAG OUTSIDE LET *) val V1fmt = formatExp (G, V1) (* GEN END TAG OUTSIDE LET *)
        (* GEN BEGIN TAG OUTSIDE LET *) val V2fmt = formatExp (G, V2) (* GEN END TAG OUTSIDE LET *)
        (* GEN BEGIN TAG OUTSIDE LET *) val diff = F.Vbox0 0 1
                   [F.String "Expected:", F.Space, V2fmt, F.Break,
                    F.String "Inferred:", F.Space, V1fmt] (* GEN END TAG OUTSIDE LET *)
        (* GEN BEGIN TAG OUTSIDE LET *) val diff = (case Print.evarCnstrsToStringOpt (Xnames)
                      of NONE => F.makestring_fmt diff
                       | SOME(cnstrs) => F.makestring_fmt diff ^
                                         "\nConstraints:\n" ^ cnstrs) (* GEN END TAG OUTSIDE LET *)
      in
        error (r2, "Type mismatch\n"
                   ^ diff ^ "\n"
                   ^ problem_msg ^ "\n"
                   ^ location_msg)
      end (* GEN END FUNCTION EXPRESSION *))

  fun delayAmbiguous (G, U, r, msg) =
      addDelayed ((* GEN BEGIN FUNCTION EXPRESSION *) fn () =>
      let
        (* GEN BEGIN TAG OUTSIDE LET *) val Ufmt = formatExp (G, U) (* GEN END TAG OUTSIDE LET *)
        (* GEN BEGIN TAG OUTSIDE LET *) val amb = F.HVbox [F.String "Inferred:", F.Space, formatExp (G, U)] (* GEN END TAG OUTSIDE LET *)
      in
        error (r, "Ambiguous reconstruction\n"
                  ^ F.makestring_fmt amb ^ "\n"
                  ^ msg)
      end (* GEN END FUNCTION EXPRESSION *))

  fun unifyIdem x =
      let
        (* this reset should be unnecessary -- for safety only *)
        (* GEN BEGIN TAG OUTSIDE LET *) val _ = Unify.reset () (* GEN END TAG OUTSIDE LET *)
        (* GEN BEGIN TAG OUTSIDE LET *) val _ = Unify.unify x
                handle e as Unify.Unify _ =>
                       (Unify.unwind ();
                        raise e) (* GEN END TAG OUTSIDE LET *)
        (* GEN BEGIN TAG OUTSIDE LET *) val _ = Unify.reset () (* GEN END TAG OUTSIDE LET *)
      in
        ()
      end

  fun unifiableIdem x =
      let
        (* this reset should be unnecessary -- for safety only *)
        (* GEN BEGIN TAG OUTSIDE LET *) val _ = Unify.reset () (* GEN END TAG OUTSIDE LET *)
        (* GEN BEGIN TAG OUTSIDE LET *) val ok = Unify.unifiable x (* GEN END TAG OUTSIDE LET *)
        (* GEN BEGIN TAG OUTSIDE LET *) val _ = if ok then Unify.reset () else Unify.unwind () (* GEN END TAG OUTSIDE LET *)
      in
        ok
      end

  (* tracing code *)

  datatype trace_mode = Progressive | Omniscient
  (* GEN BEGIN TAG OUTSIDE LET *) val trace = ref false (* GEN END TAG OUTSIDE LET *)
  (* GEN BEGIN TAG OUTSIDE LET *) val traceMode = ref Omniscient (* GEN END TAG OUTSIDE LET *)

  fun report f = case !traceMode of Progressive => f ()
                                  | Omniscient => addDelayed f

  fun reportMismatch (G, Vs1, Vs2, problem_msg) =
      report ((* GEN BEGIN FUNCTION EXPRESSION *) fn () =>
      let
        (* GEN BEGIN TAG OUTSIDE LET *) val Xs = Abstract.collectEVars (G, Vs2,
                 Abstract.collectEVars (G, Vs1, nil)) (* GEN END TAG OUTSIDE LET *)
        (* GEN BEGIN TAG OUTSIDE LET *) val Xnames = List.map ((* GEN BEGIN FUNCTION EXPRESSION *) fn X => (X, Names.evarName (IntSyn.Null, X)) (* GEN END FUNCTION EXPRESSION *)) Xs (* GEN END TAG OUTSIDE LET *)
        (* GEN BEGIN TAG OUTSIDE LET *) val eqnsFmt = F.HVbox [F.String "|?", F.Space, formatExp (G, EClo Vs1),
                               F.Break, F.String "=", F.Space, formatExp (G, EClo Vs2)] (* GEN END TAG OUTSIDE LET *)
        (* GEN BEGIN TAG OUTSIDE LET *) val _ = Msg.message (F.makestring_fmt eqnsFmt ^ "\n") (* GEN END TAG OUTSIDE LET *)
        (* GEN BEGIN TAG OUTSIDE LET *) val _ = reportConstraints Xnames (* GEN END TAG OUTSIDE LET *)
        (* GEN BEGIN TAG OUTSIDE LET *) val _ = Msg.message ("Failed: " ^ problem_msg ^ "\n"
                       ^ "Continuing with subterm replaced by _\n") (* GEN END TAG OUTSIDE LET *)
      in
        ()
      end (* GEN END FUNCTION EXPRESSION *))

  fun reportUnify' (G, Vs1, Vs2) =
      let
        (* GEN BEGIN TAG OUTSIDE LET *) val Xs = Abstract.collectEVars (G, Vs2,
                 Abstract.collectEVars (G, Vs1, nil)) (* GEN END TAG OUTSIDE LET *)
        (* GEN BEGIN TAG OUTSIDE LET *) val Xnames = List.map ((* GEN BEGIN FUNCTION EXPRESSION *) fn X => (X, Names.evarName (IntSyn.Null, X)) (* GEN END FUNCTION EXPRESSION *)) Xs (* GEN END TAG OUTSIDE LET *)
        (* GEN BEGIN TAG OUTSIDE LET *) val eqnsFmt = F.HVbox [F.String "|?", F.Space, formatExp (G, EClo Vs1),
                               F.Break, F.String "=", F.Space, formatExp (G, EClo Vs2)] (* GEN END TAG OUTSIDE LET *)
        (* GEN BEGIN TAG OUTSIDE LET *) val _ = Msg.message (F.makestring_fmt eqnsFmt ^ "\n") (* GEN END TAG OUTSIDE LET *)
        (* GEN BEGIN TAG OUTSIDE LET *) val _ = unifyIdem (G, Vs1, Vs2)
                handle e as Unify.Unify msg =>
                       (Msg.message ("Failed: " ^ msg ^ "\n"
                               ^ "Continuing with subterm replaced by _\n");
                        raise e) (* GEN END TAG OUTSIDE LET *)
        (* GEN BEGIN TAG OUTSIDE LET *) val _ = reportInst Xnames (* GEN END TAG OUTSIDE LET *)
        (* GEN BEGIN TAG OUTSIDE LET *) val _ = reportConstraints Xnames (* GEN END TAG OUTSIDE LET *)
      in
        ()
      end

  fun reportUnify (G, Vs1, Vs2) =
        (case !traceMode
           of Progressive => reportUnify' (G, Vs1, Vs2)
            | Omniscient =>
                (unifyIdem (G, Vs1, Vs2)
                 handle e as Unify.Unify msg =>
                   (reportMismatch (G, Vs1, Vs2, msg);
                    raise e)))

  fun (* GEN BEGIN FUN FIRST *) reportInfer' (G, omitexact (_, _, r), U, V) =
      let
        (* GEN BEGIN TAG OUTSIDE LET *) val Xs = Abstract.collectEVars (G, (U, id),
                 Abstract.collectEVars (G, (V, id), nil)) (* GEN END TAG OUTSIDE LET *)
        (* GEN BEGIN TAG OUTSIDE LET *) val Xnames = List.map ((* GEN BEGIN FUNCTION EXPRESSION *) fn X => (X, Names.evarName (IntSyn.Null, X)) (* GEN END FUNCTION EXPRESSION *)) Xs (* GEN END TAG OUTSIDE LET *)
        (* GEN BEGIN TAG OUTSIDE LET *) val omit = F.HVbox [F.String "|-", F.Space, F.String "_", F.Space,
                            F.String "==>", F.Space, formatExp (G, U), F.Break,
                            F.String ":", F.Space, formatExp (G, V)] (* GEN END TAG OUTSIDE LET *)
        (* GEN BEGIN TAG OUTSIDE LET *) val _ = Msg.message (F.makestring_fmt omit ^ "\n") (* GEN END TAG OUTSIDE LET *)
        (* GEN BEGIN TAG OUTSIDE LET *) val _ = reportConstraints Xnames (* GEN END TAG OUTSIDE LET *)
      in
        ()
      end (* GEN END FUN FIRST *)
    | (* GEN BEGIN FUN BRANCH *) reportInfer' (G, mismatch (tm1, tm2, _, _), U, V) =
        reportInfer' (G, tm2, U, V) (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) reportInfer' (G, hastype _, U, V) = () (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) reportInfer' (G, tm, U, V) =
      let
        (* GEN BEGIN TAG OUTSIDE LET *) val Xs = Abstract.collectEVars (G, (U, id),
                 Abstract.collectEVars (G, (V, id), nil)) (* GEN END TAG OUTSIDE LET *)
        (* GEN BEGIN TAG OUTSIDE LET *) val Xnames = List.map ((* GEN BEGIN FUNCTION EXPRESSION *) fn X => (X, Names.evarName (IntSyn.Null, X)) (* GEN END FUNCTION EXPRESSION *)) Xs (* GEN END TAG OUTSIDE LET *)
        (* GEN BEGIN TAG OUTSIDE LET *) val judg = F.HVbox [F.String "|-", F.Space, formatExp (G, U), F.Break,
                            F.String ":", F.Space, formatExp (G, V)] (* GEN END TAG OUTSIDE LET *)
        (* GEN BEGIN TAG OUTSIDE LET *) val _ = Msg.message (F.makestring_fmt judg ^ "\n") (* GEN END TAG OUTSIDE LET *)
        (* GEN BEGIN TAG OUTSIDE LET *) val _ = reportConstraints Xnames (* GEN END TAG OUTSIDE LET *)
      in
        ()
      end (* GEN END FUN BRANCH *)

  fun reportInfer x = report ((* GEN BEGIN FUNCTION EXPRESSION *) fn () => reportInfer' x (* GEN END FUNCTION EXPRESSION *))


    (* inferExact (G, tm) = (tm', U, V)
       if  tm is approximately well typed
       and tm contains no subterm above kind level
       and tm ~:~ V1
       then tm = U-
       and  U : V
       and  U, V are most general such
       effect: as for unification *)

    fun (* GEN BEGIN FUN FIRST *) inferExactN (G, tm as internal (U, V, r)) =
          (tm, Intro U, V) (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) inferExactN (G, tm as constant (H, r)) =
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val cd = headConDec (H) (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val (E, V) = addImplicit (G, headElim H, (conDecType cd, id), conDecImp cd) (* GEN END TAG OUTSIDE LET *)
        in
          (tm, Elim E, V)
        end (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) inferExactN (G, tm as bvar (k, r)) =
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val Dec (_, V) = ctxDec (G, k) (* GEN END TAG OUTSIDE LET *)
        in
          (tm, Elim (bvarElim k), V)
        end (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) inferExactN (G, tm as evar (name, r)) =
        let
          (* externally EVars are raised elim forms *)
          (* GEN BEGIN TAG OUTSIDE LET *) val (X, V) = getEVar (name, false)
                  handle Apx.Ambiguous =>
                  let
                    (* GEN BEGIN TAG OUTSIDE LET *) val (X, V) = getEVar (name, true) (* GEN END TAG OUTSIDE LET *)
                  in
                    delayAmbiguous (G, V, r, "Free variable has ambiguous type");
                    (X, V)
                  end (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val s = Shift (ctxLength (G)) (* GEN END TAG OUTSIDE LET *) (* necessary? -kw *)
        in
          (tm, Elim (elimSub (evarElim X, s)), EClo (V, s))
        end (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) inferExactN (G, tm as fvar (name, r)) =
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val V = getFVarType (name, false)
                  handle Apx.Ambiguous =>
                  let
                    (* GEN BEGIN TAG OUTSIDE LET *) val V = getFVarType (name, true) (* GEN END TAG OUTSIDE LET *)
                  in
                    delayAmbiguous (G, V, r, "Free variable has ambiguous type");
                    V
                  end (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val s = Shift (ctxLength (G)) (* GEN END TAG OUTSIDE LET *) (* necessary? -kw *)
        in
          (tm, Elim (fvarElim (name, V, s)), EClo (V, s))
        end (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) inferExactN (G, tm as typ (r)) =
          (tm, Intro (Uni Type), Uni Kind) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) inferExactN (G, arrow (tm1, tm2)) =
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val (tm1', B1, _ (* Uni Type *)) = inferExact (G, tm1) (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val D = Dec (NONE, toIntro (B1, (Uni Type, id))) (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val (tm2', B2, L) = inferExact (G, tm2) (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val V2 = toIntro (B2, (L, id)) (* GEN END TAG OUTSIDE LET *)
        in
          (arrow (tm1', tm2'), Intro (Pi ((D, No), EClo (V2, shift))), L)
        end (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) inferExactN (G, pi (tm1, tm2)) =
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val (tm1', D) = inferExactDec (G, tm1) (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val (tm2', B2, L) = inferExact (Decl (G, D), tm2) (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val V2 = toIntro (B2, (L, id)) (* GEN END TAG OUTSIDE LET *)
        in
          (pi (tm1', tm2'), Intro (Pi ((D, Maybe), V2)), L)
        end (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) inferExactN (G, lam (tm1, tm2)) =
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val (tm1', D) = inferExactDec (G, tm1) (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val (tm2', B2, V2) = inferExact (Decl (G, D), tm2) (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val U2 = toIntro (B2, (V2, id)) (* GEN END TAG OUTSIDE LET *)
        in
          (lam (tm1', tm2'), Intro (Lam (D, U2)), Pi ((D, Maybe), V2))
        end (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) inferExactN (G, app (tm1, tm2)) =
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val (tm1', B1, V1) = inferExact (G, tm1) (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val E1 = toElim (B1) (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val (Pi ((Dec (_, Va), _), Vr), s) = Whnf.whnfExpandDef (V1, id) (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val (tm2', B2) = checkExact (G, tm2, (Va, s),
                                       "Argument type did not match function domain type\n(Index object(s) did not match)") (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val U2 = toIntro (B2, (Va, s)) (* GEN END TAG OUTSIDE LET *)
        in
          (app (tm1', tm2'), Elim (elimApp (E1, U2)), EClo (Vr, Whnf.dotEta (Exp U2, s)))
        end (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) inferExactN (G, hastype (tm1, tm2)) =
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val (tm2', B2, L) = inferExact (G, tm2) (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val V = toIntro (B2, (L, id)) (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val (tm1', B1) = checkExact (G, tm1, (V, id),
                                      "Ascription did not hold\n(Index object(s) did not match)") (* GEN END TAG OUTSIDE LET *)
        in
          (hastype (tm1', tm2'), B1, V)
        end (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) inferExactN (G, mismatch (tm1, tm2, location_msg, problem_msg)) =
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val (tm1', _, V1) = inferExact (G, tm1) (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val (tm2', B, V) = inferExactN (G, tm2) (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val _ = if !trace then reportMismatch (G, (V1, id), (V, id), problem_msg) else () (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val _ = delayMismatch (G, V1, V, termRegion tm2', location_msg, problem_msg) (* GEN END TAG OUTSIDE LET *)
        in
          (mismatch (tm1', tm2', location_msg, problem_msg), B, V)
        end (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) inferExactN (G, omitapx (U, V, L, r)) =
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val V' = Apx.apxToClass (G, V, L, false)
                   handle Apx.Ambiguous =>
                   let
                     (* GEN BEGIN TAG OUTSIDE LET *) val V' = Apx.apxToClass (G, V, L, true) (* GEN END TAG OUTSIDE LET *)
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
                   end (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val U' = Apx.apxToExact (G, U, (V', id), false)
                   handle Apx.Ambiguous =>
                   let
                     (* GEN BEGIN TAG OUTSIDE LET *) val U' = Apx.apxToExact (G, U, (V', id), true) (* GEN END TAG OUTSIDE LET *)
                   in
                     delayAmbiguous (G, U', r, "Omitted " ^
                       (case Apx.whnfUni L
                          of Apx.Level 2 => "type"
                           | Apx.Level 3 => "kind") ^ " is ambiguous");
                     U'
                   end (* GEN END TAG OUTSIDE LET *)
        in
          (omitexact (U', V', r), Intro U', V')
        end (* GEN END FUN BRANCH *)

    and inferExact (G, tm) =
        if not (!trace) then inferExactN (G, tm)
        else
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val (tm', B', V') = inferExactN (G, tm) (* GEN END TAG OUTSIDE LET *)
        in
          reportInfer (G, tm', toIntro (B', (V', id)), V');
          (tm', B', V')
        end

    and inferExactDec (G, dec (name, tm, r)) =
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val (tm', B1, _ (* Uni Type *)) = inferExact (G, tm) (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val V1 = toIntro (B1, (Uni Type, id)) (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val D = Dec (name, V1) (* GEN END TAG OUTSIDE LET *)
        in
          (dec (name, tm', r), D)
        end

    and (* GEN BEGIN FUN FIRST *) checkExact1 (G, lam (dec (name, tm1, r), tm2), Vhs) =
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val (Pi ((Dec (_, Va), _), Vr), s) = Whnf.whnfExpandDef Vhs (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val ((tm1', B1, _ (* Uni Type *)), ok1) = unifyExact (G, tm1, (Va, s)) (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val V1 = toIntro (B1, (Uni Type, id)) (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val D = Dec (name, V1) (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val ((tm2', B2, V2), ok2) =
                if ok1 then checkExact1 (Decl (G, D), tm2, (Vr, dot1 s))
                else (inferExact (Decl (G, D), tm2), false) (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val U2 = toIntro (B2, (V2, id)) (* GEN END TAG OUTSIDE LET *)
        in
          ((lam (dec (name, tm1', r), tm2'), Intro (Lam (D, U2)), Pi ((D, Maybe), V2)), ok2)
        end (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) checkExact1 (G, hastype (tm1, tm2), Vhs) =
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val ((tm2', B2, L), ok2) = unifyExact (G, tm2, Vhs) (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val V = toIntro (B2, (L, id)) (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val (tm1', B1) = checkExact (G, tm1, (V, id),
                                       "Ascription did not hold\n(Index object(s) did not match)") (* GEN END TAG OUTSIDE LET *)
        in
          ((hastype (tm1', tm2'), B1, V), ok2)
        end (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) checkExact1 (G, mismatch (tm1, tm2, location_msg, problem_msg), Vhs) =
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val (tm1', _, V1) = inferExact (G, tm1) (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val ((tm2', B, V), ok2) = checkExact1 (G, tm2, Vhs) (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val _ = delayMismatch (G, V1, V, termRegion tm2', location_msg, problem_msg) (* GEN END TAG OUTSIDE LET *)
        in
          ((mismatch (tm1', tm2', location_msg, problem_msg), B, V), ok2)
        end (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) checkExact1 (G, omitapx (U, V (* = Vhs *), L, r), Vhs) =
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val V' = EClo Vhs (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val U' = Apx.apxToExact (G, U, Vhs, false)
                   handle Apx.Ambiguous =>
                   let
                     (* GEN BEGIN TAG OUTSIDE LET *) val U' = Apx.apxToExact (G, U, Vhs, true) (* GEN END TAG OUTSIDE LET *)
                   in
                     delayAmbiguous (G, U', r, "Omitted " ^
                       (case Apx.whnfUni L
                          of Apx.Level 2 => "type"
                           | Apx.Level 3 => "kind") ^ " is ambiguous");
                     U'
                   end (* GEN END TAG OUTSIDE LET *)
        in
          ((omitexact (U', V', r), Intro U', V'), true)
        end (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) checkExact1 (G, tm, Vhs) =
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val (tm', B', V') = inferExact (G, tm) (* GEN END TAG OUTSIDE LET *)
        in
          ((tm', B', V'), unifiableIdem (G, Vhs, (V', id)))
        end (* GEN END FUN BRANCH *)

    and checkExact (G, tm, Vs, location_msg) =
        if not (!trace) then
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val ((tm', B', V'), ok) = checkExact1 (G, tm, Vs) (* GEN END TAG OUTSIDE LET *)
        in
          if ok then (tm', B')
          else
          ((unifyIdem (G, (V', id), Vs);
            raise Match (* can't happen *))
           handle Unify.Unify problem_msg =>
           let
             (* GEN BEGIN TAG OUTSIDE LET *) val r = termRegion tm (* GEN END TAG OUTSIDE LET *)
             (* GEN BEGIN TAG OUTSIDE LET *) val U' = toIntro (B', (V', id)) (* GEN END TAG OUTSIDE LET *)
             (* GEN BEGIN TAG OUTSIDE LET *) val (Uapx, Vapx, Lapx) = Apx.exactToApx (U', V') (* GEN END TAG OUTSIDE LET *)
             (* GEN BEGIN TAG OUTSIDE LET *) val ((tm'', B'', _ (* Vs *)), _ (* true *)) =
                   checkExact1 (G, omitapx (Uapx, Vapx, Lapx, r), Vs) (* GEN END TAG OUTSIDE LET *)
             (* GEN BEGIN TAG OUTSIDE LET *) val _ = delayMismatch (G, V', EClo Vs, r, location_msg, problem_msg) (* GEN END TAG OUTSIDE LET *)
           in
             (mismatch (tm', tm'', location_msg, problem_msg), B'')
           end)
        end
    
        else
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val (tm', B', V') = inferExact (G, tm) (* GEN END TAG OUTSIDE LET *)
        in
          (reportUnify (G, (V', id), Vs); (tm', B'))
          handle Unify.Unify problem_msg =>
          let
            (* GEN BEGIN TAG OUTSIDE LET *) val r = termRegion tm (* GEN END TAG OUTSIDE LET *)
            (* GEN BEGIN TAG OUTSIDE LET *) val U' = toIntro (B', (V', id)) (* GEN END TAG OUTSIDE LET *)
            (* GEN BEGIN TAG OUTSIDE LET *) val (Uapx, Vapx, Lapx) = Apx.exactToApx (U', V') (* GEN END TAG OUTSIDE LET *)
            (* GEN BEGIN TAG OUTSIDE LET *) val (tm'', B'') =
                  checkExact (G, omitapx (Uapx, Vapx, Lapx, r), Vs, location_msg) (* GEN END TAG OUTSIDE LET *)
            (* GEN BEGIN TAG OUTSIDE LET *) val _ = delayMismatch (G, V', EClo Vs, r, location_msg, problem_msg) (* GEN END TAG OUTSIDE LET *)
          in
            (mismatch (tm', tm'', location_msg, problem_msg), B'')
          end
        end

    and (* GEN BEGIN FUN FIRST *) unifyExact (G, arrow (tm1, tm2), Vhs) =
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val (Pi ((Dec (_, Va), _), Vr), s) = Whnf.whnfExpandDef Vhs (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val ((tm1', B1, _ (* Uni Type *)), ok1) = unifyExact (G, tm1, (Va, s)) (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val V1 = toIntro (B1, (Uni Type, id)) (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val D = Dec (NONE, V1) (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val (tm2', B2, L) = inferExact (G, tm2) (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val V2 = toIntro (B2, (L, id)) (* GEN END TAG OUTSIDE LET *)
        in
          ((arrow (tm1', tm2'), Intro (Pi ((D, No), EClo (V2, shift))), L),
           ok1 andalso unifiableIdem (Decl (G, D), (Vr, dot1 s), (V2, shift)))
        end (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) unifyExact (G, pi (dec (name, tm1, r), tm2), Vhs) =
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val (Pi ((Dec (_, Va), _), Vr), s) = Whnf.whnfExpandDef Vhs (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val ((tm1', B1, _ (* Uni Type *)), ok1) = unifyExact (G, tm1, (Va, s)) (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val V1 = toIntro (B1, (Uni Type, id)) (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val D = Dec (name, V1) (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val ((tm2', B2, L), ok2) =
                if ok1 then unifyExact (Decl (G, D), tm2, (Vr, dot1 s))
                else (inferExact (Decl (G, D), tm2), false) (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val V2 = toIntro (B2, (L, id)) (* GEN END TAG OUTSIDE LET *)
        in
          ((pi (dec (name, tm1', r), tm2'), Intro (Pi ((D, Maybe), V2)), L), ok2)
        end (* GEN END FUN BRANCH *)
        (* lam impossible *)
      | (* GEN BEGIN FUN BRANCH *) unifyExact (G, hastype (tm1, tm2), Vhs) =
        let
          (* Vh : L by invariant *)
          (* GEN BEGIN TAG OUTSIDE LET *) val (tm2', _ (* Uni L *), _ (* Uni (Next L) *)) = inferExact (G, tm2) (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val ((tm1', B, L), ok1) = unifyExact (G, tm1, Vhs) (* GEN END TAG OUTSIDE LET *)
        in
          ((hastype (tm1', tm2'), B, L), ok1)
        end (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) unifyExact (G, mismatch (tm1, tm2, location_msg, problem_msg), Vhs) =
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val (tm1', _, L1) = inferExact (G, tm1) (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val ((tm2', B, L), ok2) = unifyExact (G, tm2, Vhs) (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val _ = delayMismatch (G, L1, L, termRegion tm2', location_msg, problem_msg) (* GEN END TAG OUTSIDE LET *)
        in
          ((mismatch (tm1', tm2', location_msg, problem_msg), B, L), ok2)
        end (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) unifyExact (G, omitapx (V (* = Vhs *), L, nL (* Next L *), r), Vhs) =
        let
          (* cannot raise Ambiguous *)
          (* GEN BEGIN TAG OUTSIDE LET *) val L' = Apx.apxToClass (G, L, nL, false) (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val V' = EClo Vhs (* GEN END TAG OUTSIDE LET *)
        in
          ((omitexact (V', L', r), Intro V', L'), true)
        end (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) unifyExact (G, tm, Vhs) =
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val (tm', B', L') = inferExact (G, tm) (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val V' = toIntro (B', (L', id)) (* GEN END TAG OUTSIDE LET *)
        in
          ((tm', B', L'), unifiableIdem (G, Vhs, (V', id)))
        end (* GEN END FUN BRANCH *)

    fun (* GEN BEGIN FUN FIRST *) occElim (constant (H, r), os, rs, i) =
        let
          (* should probably treat a constant with Foreign
             attribute as a redex *)
          (* GEN BEGIN TAG OUTSIDE LET *) val r' = List.foldr Paths.join r rs (* GEN END TAG OUTSIDE LET *)
        in
          (Paths.root (r', Paths.leaf r, conDecImp (headConDec H), i, os), r')
        end (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) occElim (bvar (k, r), os, rs, i) =
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val r' = List.foldr Paths.join r rs (* GEN END TAG OUTSIDE LET *)
        in
          (Paths.root (r', Paths.leaf r, 0, i, os), r')
        end (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) occElim (fvar (name, r), os, rs, i) =
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val r' = List.foldr Paths.join r rs (* GEN END TAG OUTSIDE LET *)
        in
          (Paths.root (r', Paths.leaf r, 0, i, os), r')
        end (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) occElim (app (tm1, tm2), os, rs, i) =
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val (oc2, r2) = occIntro tm2 (* GEN END TAG OUTSIDE LET *)
        in
          occElim (tm1, Paths.app (oc2, os), r2::rs, i+1)
        end (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) occElim (hastype (tm1, tm2), os, rs, i) = occElim (tm1, os, rs, i) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) occElim (tm, os, rs, i) =
        (* this is some kind of redex or evar-under-substitution
           also catches simple introduction forms like `type' *)
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val r' = List.foldr Paths.join (termRegion tm) rs (* GEN END TAG OUTSIDE LET *)
        in
          (Paths.leaf r', r')
        end (* GEN END FUN BRANCH *)

    and (* GEN BEGIN FUN FIRST *) occIntro (arrow (tm1, tm2)) =
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val (oc1, r1) = occIntro tm1 (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val (oc2, r2) = occIntro tm2 (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val r' = Paths.join (r1, r2) (* GEN END TAG OUTSIDE LET *)
        in
          (Paths.bind (r', SOME oc1, oc2), r')
        end (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) occIntro (pi (dec (name, tm1, r), tm2)) =
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val (oc1, r1) = occIntro tm1 (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val (oc2, r2) = occIntro tm2 (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val r' = Paths.join (r, r2) (* GEN END TAG OUTSIDE LET *)
        in
          (* not quite consistent with older implementation for dec0 *)
          (Paths.bind (r', SOME oc1, oc2), r')
        end (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) occIntro (lam (dec (name, tm1, r), tm2)) =
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val (oc1, r1) = occIntro tm1 (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val (oc2, r2) = occIntro tm2 (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val r' = Paths.join (r, r2) (* GEN END TAG OUTSIDE LET *)
        in
          (* not quite consistent with older implementation for dec0 *)
          (Paths.bind (r', SOME oc1, oc2), r')
        end (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) occIntro (hastype (tm1, tm2)) = occIntro tm1 (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) occIntro (tm) =
        let
          (* still doesn't work quite right for the location -> occurrence map? *)
          (* GEN BEGIN TAG OUTSIDE LET *) val (oc, r) = occElim (tm, Paths.nils, nil, 0) (* GEN END TAG OUTSIDE LET *)
        in
          (oc, r)
        end (* GEN END FUN BRANCH *)

    fun (* GEN BEGIN FUN FIRST *) inferExactJob (G, jnothing) = JNothing (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) inferExactJob (G, jand (j1, j2)) =
          JAnd (inferExactJob (G, j1), inferExactJob (G, j2)) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) inferExactJob (G, jwithctx (g, j)) =
        let
          fun (* GEN BEGIN FUN FIRST *) ie (Null) = (G, Null) (* GEN END FUN FIRST *)
            | (* GEN BEGIN FUN BRANCH *) ie (Decl (g, tm)) =
              let
                (* GEN BEGIN TAG OUTSIDE LET *) val (G', Gresult) = ie (g) (* GEN END TAG OUTSIDE LET *)
                (* GEN BEGIN TAG OUTSIDE LET *) val (_, D) = inferExactDec (G', tm) (* GEN END TAG OUTSIDE LET *)
              in
                (Decl (G', D), Decl (Gresult, D))
              end (* GEN END FUN BRANCH *)
          (* GEN BEGIN TAG OUTSIDE LET *) val (G', Gresult) = ie (g) (* GEN END TAG OUTSIDE LET *)
        in
          JWithCtx (Gresult, inferExactJob (G', j))
        end (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) inferExactJob (G, jterm (tm)) =
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val (tm', B, V) = inferExact (G, tm) (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val U = toIntro (B, (V, id)) (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val (oc, r) = occIntro (tm') (* GEN END TAG OUTSIDE LET *)
          fun (* GEN BEGIN FUN FIRST *) iu (Uni Type) = Kind (* GEN END FUN FIRST *)
            | (* GEN BEGIN FUN BRANCH *) iu (Pi (_, V)) = iu V (* GEN END FUN BRANCH *)
            | (* GEN BEGIN FUN BRANCH *) iu (Root _) = Type (* GEN END FUN BRANCH *)
            | (* GEN BEGIN FUN BRANCH *) iu (Redex (V, _)) = iu V (* GEN END FUN BRANCH *)
            | (* GEN BEGIN FUN BRANCH *) iu (Lam (_, V)) = iu V (* GEN END FUN BRANCH *)
            | (* GEN BEGIN FUN BRANCH *) iu (EClo (V, _)) = iu V (* GEN END FUN BRANCH *)
              (* others impossible *)
        in
          JTerm ((U, oc), V, iu V)
        end (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) inferExactJob (G, jclass (tm)) =
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val (tm', B, L) = inferExact (G, tm) (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val V = toIntro (B, (L, id)) (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val (oc, r) = occIntro (tm') (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val (Uni L, _) = Whnf.whnf (L, id) (* GEN END TAG OUTSIDE LET *)
        in
          JClass ((V, oc), L)
        end (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) inferExactJob (G, jof (tm1, tm2)) =
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val (tm2', B2, L2) = inferExact (G, tm2) (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val V2 = toIntro (B2, (L2, id)) (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val (tm1', B1) = checkExact (G, tm1, (V2, id),
                                       "Ascription in declaration did not hold\n"
                                       ^ "(Index object(s) did not match)") (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val U1 = toIntro (B1, (V2, id)) (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val (oc2, r2) = occIntro tm2' (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val (oc1, r1) = occIntro tm1' (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val (Uni L2, _) = Whnf.whnf (L2, id) (* GEN END TAG OUTSIDE LET *)
        in
          JOf ((U1, oc1), (V2, oc2), L2)
        end (* GEN END FUN BRANCH *)

      | (* GEN BEGIN FUN BRANCH *) inferExactJob (G, jof' (tm1, V2)) =
        let
      (*          val (tm2', B2, L2) = inferExact (G, tm2)
          val V2 = toIntro (B2, (L2, id)) *)
          (* GEN BEGIN TAG OUTSIDE LET *) val (tm1', B1) = checkExact (G, tm1, (V2, id),
                                       "Ascription in declaration did not hold\n"
                                       ^ "(Index object(s) did not match)") (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val U1 = toIntro (B1, (V2, id)) (* GEN END TAG OUTSIDE LET *)
      (*          val (oc2, r2) = occIntro tm2' *)
          (* GEN BEGIN TAG OUTSIDE LET *) val (oc1, r1) = occIntro tm1' (* GEN END TAG OUTSIDE LET *)
      (*          val (Uni L2, _) = Whnf.whnf (L2, id) *)
        in
          JOf ((U1, oc1), (V2, oc1), Type)
        end (* GEN END FUN BRANCH *)

    fun recon' (j) =
        let
          (* we leave it to the context to call Names.varReset
             reason: this code allows reconstructing terms containing
             existing EVars, and future developments might use that *)
          (* context must already have called resetErrors *)
          (* GEN BEGIN TAG OUTSIDE LET *) val _ = Apx.varReset () (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val _ = varReset () (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val j' = inferApxJob (Null, j) (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val _ = clearDelayed () (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val j'' = inferExactJob (Null, j') (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val _ = runDelayed () (* GEN END TAG OUTSIDE LET *)
          (* we leave it to the context to call checkErrors
             reason: the caller may want to do further processing on
             the "best effort" result returned, even if there were
             errors *)
        in
          j''
        end

    fun recon (j) = (queryMode := false; recon' j)
    fun reconQuery (j) = (queryMode := true; recon' j)

    (* Invariant, G must be named! *)
    fun reconWithCtx' (G, j) =
        let
          (* we leave it to the context to call Names.varReset
             reason: this code allows reconstructing terms containing
             existing EVars, and future developments might use that *)
          (* context must already have called resetErrors *)
          (* GEN BEGIN TAG OUTSIDE LET *) val _ = Apx.varReset () (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val _ = varReset () (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val j' = inferApxJob' (G, j) (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val _ = clearDelayed () (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val j'' = inferExactJob (G, j') (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val _ = runDelayed () (* GEN END TAG OUTSIDE LET *)
          (* we leave it to the context to call checkErrors
             reason: the caller may want to do further processing on
             the "best effort" result returned, even if there were
             errors *)
        in
          j''
        end
    fun reconWithCtx (G, j) = (queryMode := false; reconWithCtx' (G, j))
    fun reconQueryWithCtx (G, j) = (queryMode := true; reconWithCtx' (G, j))

  fun internalInst x = raise Match
  fun externalInst x = raise Match

  end (* open IntSyn *)

end (* GEN END FUNCTOR DECL *); (* functor ReconTerm *)
