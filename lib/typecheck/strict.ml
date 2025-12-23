(* Checking Definitions for_sml Strictness *)

(* Author: Carsten Schuermann *)

module type STRICT = sig
  (*! structure IntSyn : Intsyn.INTSYN !*)
  (*! structure Paths : Paths.PATHS !*)
  exception Error of string

  val check : (IntSyn.exp * IntSyn.exp) * Paths.occConDec option -> unit
  val checkType : (int * IntSyn.exp) * Paths.occConDec option -> unit
end

(* signature STRICT *)
(* Checking Definitions for_sml Strict *)

(* Author: Carsten Schuermann *)

module Strict (Whnf : Whnf.WHNF) : STRICT = struct
  (*! structure IntSyn = IntSyn' !*)

  (*! structure Paths = Paths' !*)

  exception Error of string

  module I = IntSyn
  (* Definition of normal form (nf) --- see lambda/whnf.fun *)

  (* patSpine (k, S) = B

       Invariant:
       If  G, D |- S : V > V', S in nf
       and |D| = k
       then B iff S = (k1 ; k2 ;...; kn ; NIL), kn <= k, all ki pairwise distinct
    *)

  let rec patSpine = function
    | _, I.Nil -> true
    | k, I.App (I.Root (I.BVar k', I.Nil), S) ->
        let rec indexDistinct = function
          | I.Nil -> true
          | I.App (I.Root (I.BVar k'', I.Nil), S) ->
              k' <> k'' && indexDistinct S
          | _ -> false
        in
        k' <= k && patSpine (k, S) && indexDistinct S
    | _ -> false
  (* strictExp (k, p, U) = B

       Invariant:
       If  G, D |- U : V
       and U is in nf (normal form)
       and |D| = k
       then B iff U is strict in p
    *)

  let rec strictExp = function
    | _, _, I.Uni _ -> false
    | k, p, I.Lam (D, U) -> strictDec (k, p, D) || strictExp (k + 1, p + 1, U)
    | k, p, I.Pi ((D, _), U) ->
        strictDec (k, p, D) || strictExp (k + 1, p + 1, U)
    | k, p, I.Root (H, S) -> (
        match H with
        | I.BVar k' ->
            if k' = p then patSpine (k, S)
            else if k' <= k then strictSpine (k, p, S)
            else false
        | I.Const c -> strictSpine (k, p, S)
        | I.Def d -> strictSpine (k, p, S)
        | I.FgnConst (cs, conDec) -> strictSpine (k, p, S))
    | k, p, I.FgnExp (cs, ops) -> false

  and strictSpine = function
    | _, _, I.Nil -> false
    | k, p, I.App (U, S) -> strictExp (k, p, U) || strictSpine (k, p, S)

  and strictDec (k, p, I.Dec (_, V)) = strictExp (k, p, V)
  (* strictArgParm (p, U) = B

       Traverses the flexible abstractions in U.

       Invariant:
       If   G |- U : V
       and  G |- p : V'
       and  U is in nf
       then B iff argument parameter p occurs in strict position in U
                  which starts with argument parameters
    *)

  let rec strictArgParm = function
    | p, U -> strictExp (0, p, U)
    | p, U -> strictExp (0, p, U)
    | p, U -> strictExp (0, p, U)
    | p, I.Lam (D, U) -> strictArgParm (p + 1, U)

  let rec occToString = function
    | Some ocd, occ -> Paths.wrap (Paths.occToRegionDef1 ocd occ, "")
    | None, occ -> "Error: "

  let rec decToVarName = function
    | I.Dec (None, _) -> "implicit variable"
    | I.Dec (Some x, _) -> "variable " ^ x
  (* strictTop ((U, V), ocdOpt) = ()

       Invariant:
       condec has form c = U : V where . |- U : V
       and U is in nf (normal form)
       then function returns () if U every argument parameter of U
            has at least one strict and rigid occurrence in U
       raises Error otherwise

       ocdOpt is an optional occurrence tree for_sml condec for_sml error messages
    *)

  let rec strictTop ((U, V), ocdOpt) =
    let rec strictArgParms = function
      | I.Root (I.BVar _, _), _, occ ->
          raise
            (Error (occToString (ocdOpt, occ) ^ "Head not rigid, use %abbrev"))
      | I.Root _, _, _ -> ()
      | I.Pi _, _, _ -> ()
      | I.FgnExp _, _, _ -> ()
      | I.Lam (D, U'), I.Pi (_, V'), occ ->
          if strictArgParm (1, U') then strictArgParms (U', V', Paths.body occ)
          else
            raise
              (Error
                 (occToString (ocdOpt, occ)
                 ^ "No strict occurrence of " ^ decToVarName D ^ ", use %abbrev"
                 ))
      | U, V, occ ->
          strictArgParms (U, Whnf.normalize (Whnf.expandDef (V, I.id)), occ)
    in
    strictArgParms (U, V, Paths.top)

  let rec occursInType ((i, V), ocdOpt) =
    let rec oit = function
      | (0, V), occ -> ()
      | (i, I.Pi ((D, P), V)), occ -> (
          match Abstract.piDepend ((D, P), V) with
          | I.Pi ((D', I.Maybe), V) -> oit ((i - 1, V), Paths.body occ)
          | _ ->
              raise
                (Error
                   (occToString (ocdOpt, occ)
                   ^ "No occurrence of " ^ decToVarName D
                   ^ " in type, use %abbrev")))
      | _ -> ()
    in
    oit ((i, V), Paths.top)

  let check = strictTop
  let checkType = occursInType
end

(* functor Strict *)
