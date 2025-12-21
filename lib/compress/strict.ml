module Strict = struct
  open Syntax

  exception EtaContract
  (* val eta_contract_var : spineelt -> int
      if the spine element given is an ordinary spine element (i.e. an Elt)
      that is an eta-expansion of the deBruijn index n,
      then returns n. Otherwise raises EtaContract.
    *)

  let rec eta_contract_var = function
    | Elt t -> eta_contract_var' 0 t
    | _ -> raise EtaContract

  and eta_contract_var' = function
    | n, ATerm (ARoot (Var n', s)) ->
        let s' = map eta_contract_var s in
        let rec decreasing_list = function
          | 0, [] -> true
          | n, h :: tl -> n - 1 = h && decreasing_list (n - 1) tl
          | _, _ -> false
        in
        if decreasing_list n s' then n' - n else raise EtaContract
    | n, NTerm (Lam t) -> eta_contract_var' (n + 1) t
    | _, _ -> raise EtaContract

  let rec pattern_spine' = function
    | D, [] -> true
    | D, n :: s ->
        let rec isn x = x = n in
        let rec hasn s = List.exists isn s in
        hasn D && (not (hasn s)) && pattern_spine' (D, s)

  let rec pattern_spine (D, s) =
    try pattern_spine' (D, map eta_contract_var s) with EtaContract -> false

  let rec spine_occ = function
    | n, (D, []) -> false
    | n, (D, Elt t :: s) -> term_occ n (D, t) || spine_occ n (D, s)
    | n, (D, AElt t :: s) -> aterm_occ n (D, t) || spine_occ n (D, s)
    | n, (D, Ascribe (t, a) :: s) ->
        nterm_occ n (D, t) || type_occ n (D, a) || spine_occ n (D, s)
    | n, (D, Omit :: s) -> false

  and term_occ = function
    | n, (D, NTerm t) -> nterm_occ n (D, t)
    | n, (D, ATerm t) -> aterm_occ n (D, t)

  and nterm_occ = function
    | n, (D, Lam t) -> term_occ (n + 1) (0 :: map (fun x -> x + 1) D, t)
    | n, (D, NRoot (h, s)) -> root_occ n (D, h, s)

  and aterm_occ = function
    | n, (D, ARoot (h, s)) -> root_occ n (D, h, s)
    | n, (D, ERoot _) -> false

  and root_occ = function
    | n, (D, Var n', s) ->
        if n = n' (* n = n' precludes n in D, right? *) then pattern_spine (D, s)
        else List.exists (fun x -> x = n') D && spine_occ n (D, s)
    | n, (D, Const n', s) -> spine_occ n (D, s)

  and type_occ = function
    | n, (D, TRoot (_, s)) -> spine_occ n (D, s)
    | n, (D, TPi (_, a, b)) ->
        type_occ n (D, a)
        ||
        (* PERF: suspend these context shifts, do them at the end *)
        type_occ (n + 1) (0 :: map (fun x -> x + 1) D, b)
  (* toplevel strictness judgments *)

  let rec check_strict_type' = function
    | n, p, TRoot (n', s) -> if p then false else spine_occ n ([], s)
    | n, p, TPi (PLUS, a, b) ->
        type_occ n ([], a) || check_strict_type' (n + 1) p b
    | n, p, TPi (_, a, b) -> check_strict_type' (n + 1) p b

  let rec check_strict_kind' = function
    | n, Type -> false
    | n, KPi (PLUS, a, k) -> type_occ n ([], a) || check_strict_kind' (n + 1) k
    | n, KPi (_, a, k) -> check_strict_kind' (n + 1) k
  (* p is whether we should imagine we are checking a c+ (rather than c-) constant *)

  let rec check_strict_type p b = check_strict_type' 0 p b
  let rec check_strict_kind k = check_strict_kind' 0 k
end
