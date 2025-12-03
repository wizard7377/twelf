(* Terminiation and Reduction Order *)
(* Author: Carsten Schuermann *)
(* Modified: Brigitte Pientka *)

let recctor Order ((*! module IntSyn' : INTSYN !*)
               module Table : TABLE where type key = int)
  : ORDER =
struct
  (*! module IntSyn = IntSyn' !*)

  exception Error of string


  type 'a Order =                   (* Orders                     *)
      Arg of 'a                         (* O ::= x                    *)
    | Lex of 'a Order list              (*     | {O1 .. On}           *)
    | Simul of 'a Order list            (*     | [O1 .. On]           *)


  type predicate =
      Less of int Order * int Order
    | Leq of int Order * int Order
    | Eq of int Order * int Order

  (* Mutual dependencies in call patterns:                            *)
  (* A call pattern   (a1 P1) .. (ai Pi) .. (an Pn)   expresses       *)
  (* that the proof of ai can refer to                                *)
  (*   ih a1 .. ai, as long as the arguments are strictly smaller     *)
  (* and to                                                           *)
  (*   ih a(i+1) .. an as long as the arguments are smaller or equal  *)
  (* then the ones of ai.                                             *)

  type mutual =                     (* Mutual dependencies        *)
      Empty                             (* C ::= .                    *)
    | LE of IntSyn.cid * Mutual         (*     |  <= (a) C            *)
    | LT of IntSyn.cid * Mutual         (*     |  > (a) C             *)

  type tDec =                       (* Termination declaration    *)
      TDec of int Order * Mutual        (* TDec ::= (O, C)            *)

  type rDec =                       (* Reduction declaration      *)
      RDec of Predicate * Mutual        (* RDec ::= (P, C)            *)

  local
    module I = IntSyn
    let OrderTable : TDec Table.Table = Table.new(0)
    let RedOrderTable : RDec Table.Table = Table.new(0)

    fun reset () = Table.clear OrderTable
    fun resetROrder () = Table.clear RedOrderTable

    fun install (cid, O) = Table.insert OrderTable (cid, O)
    fun uninstall cid =
        case Table.lookup OrderTable cid
          of NONE => false
           | SOME _ => (Table.delete OrderTable cid ; true)
    fun installROrder (cid, P) = Table.insert RedOrderTable (cid, P)
    fun uninstallROrder cid =
        case Table.lookup RedOrderTable cid
          of NONE => false
           | SOME _ => (Table.delete RedOrderTable cid ; true)


    fun lookup cid = Table.lookup OrderTable cid
    fun lookupROrder cid = Table.lookup RedOrderTable cid

    fun selLookup a =
        case lookup a
          of NONE => raise Error ("No termination order assigned for " ^ I.conDecName (I.sgnLookup a))
           | SOME (TDec (S, _)) => S

    fun selLookupROrder a =
        case lookupROrder a
          of NONE => raise Error ("No reduction order assigned for " ^ I.conDecName (I.sgnLookup a) ^ ".")
           | SOME (RDec (P, _)) => P

    fun mutLookupROrder a =
        case lookupROrder a
          of NONE => raise Error ("No order assigned for " ^ I.conDecName (I.sgnLookup a) ^ ".")
           | SOME (RDec (_, M)) => M

    fun mutLookup a =
        case lookup a
          of NONE => raise Error ("No order assigned for " ^ I.conDecName (I.sgnLookup a))
           | SOME (TDec (_, M)) => M

    (* mutual a = a's

       Invariant:
       If   a occurs in a call pattern (a1 P1) .. (an Pn)
       then a's = a1 .. an
    *)
    fun mutual a =
        let
          fun mutual' (Empty, a's) = a's
            | mutual' (LE (a, M), a's) = mutual' (M, a :: a's)
            | mutual' (LT (a, M), a's) = mutual' (M, a :: a's)
        in
          mutual' (mutLookup a, nil)
        end

    (* closure (a1s, a2s) = a3s

       Invariant:
       If   a1s  and a2s are lists of type families,
       then a3s is a list of type fmailies, which are mutual recursive to each other
       and include a1s and a2s.
    *)
    fun closure (nil, a2s) = a2s
      | closure (a :: a1s, a2s) =
        if List.exists (fn a' => a = a') a2s
          then closure (a1s, a2s)
        else closure (mutual a @ a1s, a :: a2s)

  in
    let reset = reset
    let resetROrder = resetROrder
    let install = install
    let uninstall = uninstall
    let installROrder = installROrder
    let uninstallROrder = uninstallROrder
    let selLookup = selLookup
    let selLookupROrder = selLookupROrder
    let mutLookup = mutLookup
    let closure = fun a -> closure ([a], nil)
  end (* local *)
end; (* functor Order *)
