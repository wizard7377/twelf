(* Checking Definitions for Strict *)
(* Author: Carsten Schuermann *)

module Strict ((*! module IntSyn' : INTSYN !*)
                (Whnf : WHNF): STRICT =
                (*! sharing Whnf.IntSyn = IntSyn' !*)
                (*! module Paths' : PATHS !*)
struct
  (*! module IntSyn = IntSyn' !*)
  (*! module Paths = Paths' !*)

  exception Error of string

  local
    module I = IntSyn

    (* Definition of normal form (nf) --- see lambda/whnf.fun *)

    (* patSpine (k, S) = B

       Invariant:
       If  G, D |- S : V > V', S in nf
       and |D| = k
       then B iff S = (k1 ; k2 ;...; kn ; NIL), kn <= k, all ki pairwise distinct
    *)
    let rec patSpine = function (_, I.Nil) -> true
      | (k, I.App (I.Root (I.BVar (k'), I.Nil), S)) -> 
        (* possibly eta-contract? -fp *)
        let fun indexDistinct (I.Nil) = true
              | indexDistinct (I.App (I.Root (I.BVar (k''), I.Nil), S)) =
                  k' <> k'' andalso indexDistinct S
              | indexDistinct _ = false
        in
          k' <= k andalso patSpine (k, S) andalso indexDistinct S
        end
      | _ -> false

    (* strictExp (k, p, U) = B

       Invariant:
       If  G, D |- U : V
       and U is in nf (normal form)
       and |D| = k
       then B iff U is strict in p
    *)
    let rec strictExp = function (_, _, I.Uni _) -> false
      | (k, p, I.Lam (D, U)) -> 
          (* checking D in this case might be redundant -fp *)
          strictDec (k, p, D) orelse strictExp (k+1, p+1, U)
      | (k, p, I.Pi ((D, _), U)) -> 
          strictDec (k, p, D) orelse strictExp (k+1, p+1, U)
      | (k, p, I.Root (H, S)) -> 
          (case H
             of (I.BVar (k')) =>
                if (k' = p) then patSpine (k, S)
                else if (k' <= k) then strictSpine (k, p, S)
                     else false
              | (I.Const (c)) => strictSpine (k, p, S)
              | (I.Def (d))  => strictSpine (k, p, S)
              | (I.FgnConst (cs, conDec)) => strictSpine (k, p, S))
              (* no other cases possible *)
      | (k, p, I.FgnExp (cs, ops)) -> false
          (* this is a hack - until we investigate this further   -rv *)
    (* no other cases possible *)

    (* strictSpine (k, S) = B

       Invariant:
       If  G, D |- S : V > W
       and S is in nf (normal form)
       and |D| = k
       then B iff S is strict in k
    *)
    and strictSpine (_, _, I.Nil) = false
      | strictSpine (k, p, I.App (U, S)) =
          strictExp (k, p, U) orelse strictSpine (k, p, S)

    and strictDec (k, p, I.Dec (_, V)) =
          strictExp (k, p, V)

    (* strictArgParm (p, U) = B

       Traverses the flexible abstractions in U.

       Invariant:
       If   G |- U : V
       and  G |- p : V'
       and  U is in nf
       then B iff argument parameter p occurs in strict position in U
                  which starts with argument parameters
    *)
    let rec strictArgParm = function (p, U as I.Root _) -> strictExp (0, p, U)
      | (p, U as I.Pi _) -> strictExp (0, p, U)
      | (p, U as I.FgnExp _) -> strictExp (0, p, U)
      | (p, I.Lam (D, U)) -> strictArgParm (p+1, U)

    let rec occToString = function (SOME(ocd), occ) -> Paths.wrap (Paths.occToRegionDef1 ocd occ, "")
      | (NONE, occ) -> "Error: "

    let rec decToVarName = function (I.Dec (NONE, _)) -> "implicit variable"
      | (I.Dec (SOME(x), _)) -> "variable " ^ x

    (* strictTop ((U, V), ocdOpt) = ()

       Invariant:
       condec has form c = U : V where . |- U : V
       and U is in nf (normal form)
       then function returns () if U every argument parameter of U
            has at least one strict and rigid occurrence in U
       raises Error otherwise

       ocdOpt is an optional occurrence tree for condec for error messages
    *)
    let rec strictTop ((U, V), ocdOpt) =
        let fun strictArgParms (I.Root (I.BVar _, _), _, occ) =
                raise Error (occToString (ocdOpt, occ) ^ "Head not rigid, use %abbrev")
              | strictArgParms (I.Root _, _, _) = ()
              | strictArgParms (I.Pi _, _, _) = ()
              | strictArgParms (I.FgnExp _, _, _) = ()
                  (* may not be sound in general *)
                  (* Wed Aug 25 16:39:57 2004 -fp *)
              | strictArgParms (I.Lam (D, U'), I.Pi (_, V'), occ) =
                if strictArgParm (1, U')
                  then strictArgParms (U', V', Paths.body occ)
                else raise Error (occToString (ocdOpt, occ)
                                  ^ "No strict occurrence of " ^ decToVarName D ^ ", use %abbrev")
              | strictArgParms (U as I.Lam _, V as I.Root (I.Def _, _), occ) =
                  strictArgParms (U, Whnf.normalize (Whnf.expandDef (V, I.id)), occ)

        in
          strictArgParms (U, V, Paths.top)
        end

   let rec occursInType ((i, V), ocdOpt) =
       let fun oit ((0, V), occ) = ()
             | oit ((i, I.Pi((D,P), V)), occ) =
               (case Abstract.piDepend ((D,P), V)
                  of I.Pi ((D', I.Maybe), V) => oit ((i-1, V), Paths.body occ)
                   | _ => raise Error (occToString (ocdOpt, occ)
                                       ^ "No occurrence of " ^ decToVarName D ^ " in type, use %abbrev"))
             | oit _ = ()
       in
         oit ((i, V), Paths.top)
       end

  in
    let check = strictTop
    let checkType = occursInType
  end
end;; (* functor Strict *)
