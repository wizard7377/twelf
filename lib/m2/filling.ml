(* Filling *)


(* Author: Carsten Schuermann *)


module Filling (MetaSyn' : METASYN) (MetaAbstract : METAABSTRACT) (Search : OLDSEARCH) (Whnf : WHNF) (Print : PRINT) : FILLING = struct module MetaSyn = MetaSyn'
exception Error of string
exception TimeOut
type operator = (MetaSyn.state * int) * (unit -> MetaSyn.state list)
module M = MetaSyn
module I = IntSyn
exception Success of M.state
let rec delay (search, Params) ()  = (try search Params with Search.Error s -> raise (Error s))
let rec makeAddressInit S k  = (S, k)
let rec makeAddressCont makeAddress k  = makeAddress (k + 1)
(* operators (G, GE, (V, s), abstract, makeAddress) = (OE', OL')

       Invariant:
       If   G |- s : G1   G1 |- V : type
       and  abstract is an abstraction continuation
       and  makeAddress is continuation which calculates the correct
         debruijn index of the variable being filled
       and V = {V1}...{Vn} V'
       then OE' is an operator list, OL' is a list with one operator
         where the ith O' in OE' corresponds to a function which generates ALL possible
                                      successor states instantiating - non-index variables
                                      with terms (if possible) in Vi
        and OL' is a list containing one operator which instantiates all - non-index variables
          in V' with the smallest possible terms.
    *)

let rec operators (G, GE, Vs, abstractAll, abstractEx, makeAddress)  = operatorsW (G, GE, Whnf.whnf Vs, abstractAll, abstractEx, makeAddress)
and operatorsW = function (G, GE, Vs, abstractAll, abstractEx, makeAddress) -> ([], (makeAddress 0, delay (fun Params -> (try Search.searchEx Params with Success S -> [S]), (G, GE, Vs, abstractEx)))) | (G, GE, (I.Pi ((D, P), V2), s), abstractAll, abstractEx, makeAddress) -> ( let (GO', O) = operators (I.Decl (G, I.decSub (D, s)), GE, (V2, I.dot1 s), abstractAll, abstractEx, makeAddressCont makeAddress) in  ((makeAddress 0, delay (Search.searchAll, (G, GE, (V1, s), abstractAll))) :: GO', O) )
(* createEVars (G, M) = ((G', M'), s', GE')

       Invariant:
       If   |- G ctx
       and  G |- M mtx
       then |- G' ctx
       and  G' |- M' mtx
       and  G' |- s' : G
       and  GE a list of EVars

    *)

let rec createEVars = function (M.Prefix (I.Null, I.Null, I.Null)) -> (M.Prefix (I.Null, I.Null, I.Null), I.id, []) | (M.Prefix (I.Decl (G, D), I.Decl (M, M.Top), I.Decl (B, b))) -> ( let (M.Prefix (G', M', B'), s', GE') = createEVars (M.Prefix (G, M, B)) in  (M.Prefix (I.Decl (G', I.decSub (D, s')), I.Decl (M', M.Top), I.Decl (B', b)), I.dot1 s', GE') ) | (M.Prefix (I.Decl (G, I.Dec (_, V)), I.Decl (M, M.Bot), I.Decl (B, _))) -> ( let (M.Prefix (G', M', B'), s', GE') = createEVars (M.Prefix (G, M, B)) in let X = I.newEVar (G', I.EClo (V, s')) in let X' = Whnf.lowerEVar X in  (M.Prefix (G', M', B'), I.Dot (I.Exp (X), s'), X' :: GE') )
(* expand' ((G, M), V) = (OE', OL')

       Invariant:
       If   |- G ctx
       and  G |- M mtx
       and  G |- V type
       and  V = {V1}...{Vn} V'
       then OE' is an operator list, OL' is a list with one operator
         where the ith O' in OE' corresponds to a function which generates ALL possible
                                      successor states instantiating - non-index variables
                                      with terms (if possible) in Vi
        and OL' is a list containing one operator which instantiates all - non-index variables
          in V' with the smallest possible terms.
    *)

let rec expand (S)  = ( let (M.Prefix (G', M', B'), s', GE') = createEVars (M.Prefix (G, M, B)) in let rec abstractAll acc  = (try MetaAbstract.abstract (M.State (name, M.Prefix (G', M', B'), I.EClo (V, s'))) :: acc with MetaAbstract.Error s -> acc) in let rec abstractEx ()  = try (raise (Success (MetaAbstract.abstract (M.State (name, M.Prefix (G', M', B'), I.EClo (V, s')))))) with MetaAbstract.Error s -> () in  operators (G', GE', (V, s'), abstractAll, abstractEx, makeAddressInit S) )
(* apply (S, f) = S'

       Invariant:
       S is state and f is a function constructing the successor state S'
    *)

let rec apply (_, f)  = f ()
let rec menu ((M.State (name, M.Prefix (G, M, B), V), k), Sl)  = ( (* no cases for_sml
              toSTring (G, I.Root _, k) for_sml k <> 0
            *)
let rec toString = function (G, I.Pi ((I.Dec (_, V), _), _), 0) -> Print.expToString (G, V) | (G, V, 0) -> Print.expToString (G, V) | (G, I.Pi ((D, _), V), k) -> toString (I.Decl (G, D), V, k - 1) in  "Filling   : " ^ toString (G, V, k) )
let expand = expand
let apply = apply
let menu = menu
(* local *)

 end


(* functor Filling *)

