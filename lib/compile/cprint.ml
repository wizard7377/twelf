(* Printer for_sml Compiled Syntax *)

(* Author: Iliano Cervesato *)

module type CPRINT = sig
  (*! structure IntSyn : Intsyn.INTSYN !*)
  (*! structure CompSyn : Compsyn.COMPSYN !*)
  val goalToString : string -> IntSyn.dctx * CompSyn.goal -> string
  val clauseToString : string -> IntSyn.dctx * CompSyn.resGoal -> string
  val sProgToString : unit -> string
  val dProgToString : CompSyn.dProg -> string
  val subgoalsToString : string -> IntSyn.dctx * CompSyn.conjunction -> string
end

(* signature CPRINT *)
(* Printer for_sml Compiled Syntax *)

(* Author: Iliano Cervesato *)

module CPrint
    (Print : Print.PRINT)
    (Formatter : Formatter.FORMATTER)
    (Names : Names.NAMES) : CPRINT = struct
  (*! structure IntSyn = IntSyn' !*)

  (*! structure CompSyn = CompSyn' !*)

  open CompSyn

  let rec compose = function
    | IntSyn.Null, G -> G
    | IntSyn.Decl (G, D), G' -> IntSyn.Decl (compose (G, G'), D)
  (* goalToString (G, g) where G |- g  goal *)

  let rec goalToString = function
    | t, (G, Atom p) -> t ^ "Solve.SOLVE   " ^ Print.expToString (G, p) ^ "\n"
    | t, (G, Impl (p, A, _, g)) ->
        t ^ "ASSUME  "
        ^ Print.expToString (G, A)
        ^ "\n"
        ^ clauseToString (t ^ "\t") (G, p)
        ^ goalToString t (IntSyn.Decl (G, IntSyn.Dec (None, A)), g)
        ^ "\n"
    | t, (G, All (D, g)) ->
        let D' = Names.decLUName (G, D) in
        t ^ "ALL     "
        ^ Formatter.makestring_fmt (Print.formatDec (G, D'))
        ^ "\n"
        ^ goalToString t (IntSyn.Decl (G, D'), g)
        ^ "\n"

  and auxToString = function
    | t, (G, Trivial) -> ""
    | t, (G, UnifyEq (G', p1, N, ga)) ->
        t ^ "Unify.UNIFYEqn  "
        ^ Print.expToString (compose (G', G), p1)
        ^ " = "
        ^ Print.expToString (compose (G', G), N)
        ^ "\n"
        ^ auxToString t (G, ga)

  and clauseToString = function
    | t, (G, Eq p) -> t ^ "Unify.UNIFY   " ^ Print.expToString (G, p) ^ "\n"
    | t, (G, Assign (p, ga)) ->
        t ^ "Assign.ASSIGN  "
        ^ (try Print.expToString (G, p) with _ -> "<exc>")
        ^ "\n"
        ^ auxToString t (G, ga)
    | t, (G, And (r, A, g)) ->
        clauseToString t (IntSyn.Decl (G, IntSyn.Dec (None, A)), r)
        ^ goalToString t (G, g)
    | t, (G, In (r, A, g)) ->
        let D = Names.decEName (G, IntSyn.Dec (None, A)) in
        clauseToString t (IntSyn.Decl (G, D), r)
        ^ t ^ "META    "
        ^ Print.decToString (G, D)
        ^ "\n"
        ^ goalToString t (G, g)
    | t, (G, Exists (D, r)) ->
        let D' = Names.decEName (G, D) in
        t ^ "EXISTS  "
        ^ (try Print.decToString (G, D') with _ -> "<exc>")
        ^ "\n"
        ^ clauseToString t (IntSyn.Decl (G, D'), r)
    | t, (G, Axists (D, r)) ->
        let D' = Names.decEName (G, D) in
        t ^ "EXISTS'  "
        ^ (try Print.decToString (G, D') with _ -> "<exc>")
        ^ "\n"
        ^ clauseToString t (IntSyn.Decl (G, D'), r)

  let rec subgoalsToString = function
    | t, (G, True) -> t ^ "True "
    | t, (G, Conjunct (Goal, A, Sg)) ->
        t
        ^ goalToString t (IntSyn.Decl (G, IntSyn.Dec (None, A)), Goal)
        ^ " and "
        ^ subgoalsToString t (G, Sg)
  (* conDecToString (c, clause) printed representation of static clause *)

  let rec conDecToString = function
    | c, SClause r ->
        let _ = Names.varReset IntSyn.Null in
        let name = IntSyn.conDecName (IntSyn.sgnLookup c) in
        let l = String.size name in
        name
        ^ (if l > 6 then ":\n" else ":")
        ^ clauseToString "\t" (IntSyn.Null, r)
        ^ "\n"
    | c, Void -> Print.conDecToString (IntSyn.sgnLookup c) ^ "\n\n"
  (* sProgToString () = printed representation of static program *)

  let rec sProgToString () =
    let size, _ = IntSyn.sgnSize () in
    let rec ts cid =
      if cid < size then
        conDecToString (cid, CompSyn.sProgLookup cid) ^ ts (cid + 1)
      else ""
    in
    ts 0
  (* dProgToString (G, dProg) = printed representation of dynamic program *)

  let rec dProgToString = function
    | DProg (IntSyn.Null, IntSyn.Null) -> ""
    | DProg
        ( IntSyn.Decl (G, IntSyn.Dec (Some x, _)),
          IntSyn.Decl (dPool, CompSyn.Dec (r, _, _)) ) ->
        dProgToString (DProg (G, dPool))
        ^ "\nClause    " ^ x ^ ":\n"
        ^ clauseToString "\t" (G, r)
    | DProg
        ( IntSyn.Decl (G, IntSyn.Dec (Some x, A)),
          IntSyn.Decl (dPool, CompSyn.Parameter) ) ->
        dProgToString (DProg (G, dPool))
        ^ "\nParameter " ^ x ^ ":\t"
        ^ Print.expToString (G, A)
  (* case for_sml CompSyn.BDec is still missing *)
  (* local open ... *)
end

(* functor CPrint *)
