open Basis ;; 

module Convert = struct
  open Syntax

  exception Convert of string
  exception NotFound of string

  let sigma : string list ref = ref []
  let sigmat : class_sml list ref = ref []
  let sigmap : bool list ref = ref []

  let rec clear () =
    sigma := [];
    sigmat := [];
    sigmap := []

  let rec findn = function
    | [], (v : string) -> raise (NotFound v)
    | v :: tl, v' -> if v = v' then 0 else 1 + findn tl v'

  let rec findid ctx v =
    try Var (findn ctx v) with NotFound _ -> Const (findn !sigma v)

  let rec modeconvert = function
    | Parse.MMinus -> MINUS
    | Parse.MPlus -> PLUS
    | Parse.MOmit -> OMIT

  let rec modesofclass = function
    | KClass Type -> []
    | KClass (KPi (m, _, k)) -> m :: modesofclass (KClass k)
    | TClass (TRoot _) -> []
    | TClass (TPi (m, _, a)) -> m :: modesofclass (TClass a)
  (* given a context and an external expression, returns the internal 'spine form' as a 4-tuple
   (h, mopt, p, s)
   where h is the head (Var n or Const n)
         mopt is a list of modes for_sml the arguments (MINUS, PLUS, OMIT)
         p is true iff the head is a synthesizing constant or a variable
         s is the list of arugments
*)

  let rec spine_form = function
    | G, Parse.Id s -> (
        match findid G s with
        | Var n -> (Var n, None, true, [])
        | Const n ->
            ( Const n,
              Some (modesofclass (List.nth (!sigmat, n))),
              List.nth (!sigmap, n),
              [] ))
    | G, Parse.App (t, u) ->
        let h, mopt, p, s = spine_form (G, t) in
        (h, mopt, p, s @ [ u ])
    | G, Parse.Lam _ -> raise (Convert "illegal redex")
    | G, _ -> raise (Convert "level mismatch")
  (* similar to spine_form for_sml a type family applied to a list of arguments *)

  let rec type_spine_form = function
    | G, Parse.Id s ->
        let n = findn !sigma s in
        (n, modesofclass (List.nth (!sigmat, n)), [])
    | G, Parse.App (t, u) ->
        let n, m, s = type_spine_form (G, t) in
        (n, m, s @ [ u ])
    | G, _ -> raise (Convert "level mismatch")

  let rec safezip (l1, l2) =
    if length l1 = length l2 then ListPair.zip (l1, l2)
    else raise (Convert "wrong spine length")
  (* given a context and an external expression and a mode, return a spine element or raise an exception*)

  let rec eltconvert = function
    | G, (t, MINUS) -> Elt (convert (G, t))
    | G, (Parse.Ascribe (t, a), PLUS) ->
        Ascribe (nconvert (G, t), typeconvert (G, a))
    | G, (t, PLUS) -> AElt (aconvert (G, t))
    | G, (Parse.Omit, OMIT) -> Omit
    | G, (_, OMIT) -> raise (Convert "found term expected to be omitted")

  and aconvert (G, t) =
    match convert (G, t) with
    | ATerm t' -> t'
    | NTerm _ -> raise (Convert "required atomic, found normal")

  and nconvert (G, t) =
    match convert (G, t) with
    | NTerm t' -> t'
    | ATerm _ -> raise (Convert "required normal, found atomic")

  and convert = function
    | G, Parse.Lam ((v, _), t) -> NTerm (Lam (convert (v :: G, t)))
    | G, t ->
        let h, mopt, p, s = spine_form (G, t) in
        let s' =
          map (eltconvert G)
            (match mopt with
            | None -> map (fun elt -> (elt, MINUS)) s
            | Some m -> safezip (s, m))
        in
        if p then ATerm (ARoot (h, s')) else NTerm (NRoot (h, s'))

  and typeconvert = function
    | G, Parse.Pi (m, (v, Some t), t') ->
        let ct = typeconvert (G, t) in
        let ct' = typeconvert (v :: G, t') in
        TPi (modeconvert m, ct, ct')
    | G, Parse.Pi (m, (_, None), _) ->
        raise (Convert "can't handle implicit pi")
    | G, Parse.Arrow (t, t') ->
        let ct = typeconvert (G, t) in
        let ct' = typeconvert ("" :: G, t') in
        TPi (MINUS, ct, ct')
    | G, Parse.PlusArrow (t, t') ->
        let ct = typeconvert (G, t) in
        let ct' = typeconvert ("" :: G, t') in
        TPi (PLUS, ct, ct')
    | G, a ->
        let n, m, s = type_spine_form (G, a) in
        let s' = map (eltconvert G) (safezip (s, m)) in
        TRoot (n, s')

  and kindconvert = function
    | G, Parse.Pi (m, (v, Some t), t') ->
        let ct = typeconvert (G, t) in
        let ct' = kindconvert (v :: G, t') in
        KPi (modeconvert m, ct, ct')
    | G, Parse.Arrow (t, t') ->
        let ct = typeconvert (G, t) in
        let ct' = kindconvert ("" :: G, t') in
        KPi (MINUS, ct, ct')
    | G, Parse.PlusArrow (t, t') ->
        let ct = typeconvert (G, t) in
        let ct' = kindconvert ("" :: G, t') in
        KPi (PLUS, ct, ct')
    | G, Parse.Pi (m, (_, None), _) ->
        raise (Convert "can't handle implicit pi")
    | G, Parse.Type -> Type
    | _ -> raise (Convert "level mismatch")
end
