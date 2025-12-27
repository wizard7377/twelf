open Basis

(* Termination Order *)

(* Author: Carsten Schuermann *)

module type ORDER = sig
  (*! structure IntSyn : Intsyn.INTSYN !*)
  exception Error of string

  type 'a order = Arg of 'a | Lex of 'a order list | Simul of 'a order list

  (*     | [O1 .. On]           *)
  type predicate =
    | Less of int order * int order
    | Leq of int order * int order
    | Eq of int order * int order

  (* O = O'                     *)
  type mutual = Empty | LE of IntSyn.cid * mutual | LT of IntSyn.cid * mutual

  (*     | lex order for_sml  -     *)
  type tDec = TDec of int order * mutual
  type rDec = RDec of predicate * mutual

  val reset : unit -> unit
  val resetROrder : unit -> unit
  val install : IntSyn.cid * tDec -> unit
  val uninstall : IntSyn.cid -> bool
  val installROrder : IntSyn.cid * rDec -> unit
  val uninstallROrder : IntSyn.cid -> bool
  val selLookup : IntSyn.cid -> int order
  val selLookupROrder : IntSyn.cid -> predicate
  val mutLookup : IntSyn.cid -> mutual
  val closure : IntSyn.cid -> IntSyn.cid list
end

(* signature Order.ORDER *)
(* Terminiation and Reduction Order *)

(* Author: Carsten Schuermann *)

(* Modified: Brigitte Pientka *)

module Order : Order.ORDER = struct
  (*! structure IntSyn = IntSyn' !*)

  exception Error of string

  type 'a order = Arg of 'a | Lex of 'a order list | Simul of 'a order list
  (*     | [O1 .. On]           *)

  type predicate =
    | Less of int order * int order
    | Leq of int order * int order
    | Eq of int order * int order
  (* Mutual dependencies in call patterns:                            *)

  (* A call pattern   (a1 P1) .. (ai Pi) .. (an Pn)   expresses       *)

  (* that the proof of ai can refer to                                *)

  (*   ih a1 .. ai, as the arguments are strictly smaller     *)

  (* and to                                                           *)

  (*   ih a(i+1) .. the arguments are smaller or Equal  *)

  (* then the ones of ai.                                             *)

  type mutual = Empty | LE of IntSyn.cid * mutual | LT of IntSyn.cid * mutual
  (*     |  > (a) C             *)

  type tDec = TDec of int order * mutual
  (* TDec ::= (O, C)            *)

  type rDec = RDec of predicate * mutual
  (* RDec ::= (P, C)            *)

  module I = IntSyn

  let OrderTable : tDec Table.table = Table.new_ 0
  let RedOrderTable : rDec Table.table = Table.new_ 0
  let rec reset () = Table.clear OrderTable
  let rec resetROrder () = Table.clear RedOrderTable
  let rec install (cid, O) = Table.insert OrderTable (cid, O)

  let rec uninstall cid =
    match Table.lookup OrderTable cid with
    | None -> false
    | Some _ ->
        Table.delete OrderTable cid;
        true

  let rec installROrder (cid, P) = Table.insert RedOrderTable (cid, P)

  let rec uninstallROrder cid =
    match Table.lookup RedOrderTable cid with
    | None -> false
    | Some _ ->
        Table.delete RedOrderTable cid;
        true

  let rec lookup cid = Table.lookup OrderTable cid
  let rec lookupROrder cid = Table.lookup RedOrderTable cid

  let rec selLookup a =
    match lookup a with
    | None ->
        raise
          (Error
             ("No termination order assigned for_sml "
             ^ I.conDecName (I.sgnLookup a)))
    | Some (TDec (S, _)) -> S

  let rec selLookupROrder a =
    match lookupROrder a with
    | None ->
        raise
          (Error
             ("No reduction order assigned for_sml "
             ^ I.conDecName (I.sgnLookup a)
             ^ "."))
    | Some (RDec (P, _)) -> P

  let rec mutLookupROrder a =
    match lookupROrder a with
    | None ->
        raise
          (Error
             ("No order assigned for_sml " ^ I.conDecName (I.sgnLookup a) ^ "."))
    | Some (RDec (_, M)) -> M

  let rec mutLookup a =
    match lookup a with
    | None ->
        raise
          (Error ("No order assigned for_sml " ^ I.conDecName (I.sgnLookup a)))
    | Some (TDec (_, M)) -> M
  (* mutual a = a's

       Invariant:
       If   a occurs in a call pattern (a1 P1) .. (an Pn)
       then a's = a1 .. an
    *)

  let rec mutual a =
    let rec mutual' = function
      | Empty, a's -> a's
      | LE (a, M), a's -> mutual' (M, a :: a's)
      | LT (a, M), a's -> mutual' (M, a :: a's)
    in
    mutual' (mutLookup a, [])
  (* closure (a1s, a2s) = a3s

       Invariant:
       If   a1s  and a2s are lists of type families,
       then a3s is a list of type fmailies, which are mutual recursive to each other
       and include a1s and a2s.
    *)

  let rec closure = function
    | [], a2s -> a2s
    | a :: a1s, a2s ->
        if List.exists (fun a' -> a = a') a2s then closure (a1s, a2s)
        else closure (mutual a @ a1s, a :: a2s)

  let reset = reset
  let resetROrder = resetROrder
  let install = install
  let uninstall = uninstall
  let installROrder = installROrder
  let uninstallROrder = uninstallROrder
  let selLookup = selLookup
  let selLookupROrder = selLookupROrder
  let mutLookup = mutLookup
  let closure = fun a -> closure ([ a ], [])
  (* local *)
end

(* functor Order *)
