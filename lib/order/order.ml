(* Terminiation and Reduction Order *)
(* Author: Carsten Schuermann *)
(* Modified: Brigitte Pientka *)

functor (* GEN BEGIN FUNCTOR DECL *) Order ((*! structure IntSyn' : INTSYN !*)
               structure Table : TABLE where type key = int)
  : ORDER =
struct
  (*! structure IntSyn = IntSyn' !*)

  exception Error of string


  datatype 'a order =                   (* Orders                     *)
      Arg of 'a                         (* O ::= x                    *)
    | Lex of 'a order list              (*     | {O1 .. On}           *)
    | Simul of 'a order list            (*     | [O1 .. On]           *)


  datatype predicate =
      Less of int order * int order
    | Leq of int order * int order
    | Eq of int order * int order

  (* Mutual dependencies in call patterns:                            *)
  (* A call pattern   (a1 P1) .. (ai Pi) .. (an Pn)   expresses       *)
  (* that the proof of ai can refer to                                *)
  (*   ih a1 .. ai, as long as the arguments are strictly smaller     *)
  (* and to                                                           *)
  (*   ih a(i+1) .. an as long as the arguments are smaller or equal  *)
  (* then the ones of ai.                                             *)

  datatype mutual =                     (* Mutual dependencies        *)
      Empty                             (* C ::= .                    *)
    | LE of IntSyn.cid * mutual         (*     |  <= (a) C            *)
    | LT of IntSyn.cid * mutual         (*     |  > (a) C             *)

  datatype t_dec =                       (* Termination declaration    *)
      TDec of int order * mutual        (* TDec ::= (O, C)            *)

  datatype r_dec =                       (* Reduction declaration      *)
      RDec of predicate * mutual        (* RDec ::= (P, C)            *)

  local
    structure I = IntSyn
    (* GEN BEGIN TAG OUTSIDE LET *) val OrderTable : t_dec Table.table = Table.new(0) (* GEN END TAG OUTSIDE LET *)
    (* GEN BEGIN TAG OUTSIDE LET *) val RedOrderTable : r_dec Table.table = Table.new(0) (* GEN END TAG OUTSIDE LET *)

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
          fun (* GEN BEGIN FUN FIRST *) mutual' (Empty, a's) = a's (* GEN END FUN FIRST *)
            | (* GEN BEGIN FUN BRANCH *) mutual' (LE (a, M), a's) = mutual' (M, a :: a's) (* GEN END FUN BRANCH *)
            | (* GEN BEGIN FUN BRANCH *) mutual' (LT (a, M), a's) = mutual' (M, a :: a's) (* GEN END FUN BRANCH *)
        in
          mutual' (mutLookup a, nil)
        end

    (* closure (a1s, a2s) = a3s

       Invariant:
       If   a1s  and a2s are lists of type families,
       then a3s is a list of type fmailies, which are mutual recursive to each other
       and include a1s and a2s.
    *)
    fun (* GEN BEGIN FUN FIRST *) closure (nil, a2s) = a2s (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) closure (a :: a1s, a2s) =
        if List.exists ((* GEN BEGIN FUNCTION EXPRESSION *) fn a' => a = a' (* GEN END FUNCTION EXPRESSION *)) a2s
          then closure (a1s, a2s)
        else closure (mutual a @ a1s, a :: a2s) (* GEN END FUN BRANCH *)

  in
    (* GEN BEGIN TAG OUTSIDE LET *) val reset = reset (* GEN END TAG OUTSIDE LET *)
    (* GEN BEGIN TAG OUTSIDE LET *) val resetROrder = resetROrder (* GEN END TAG OUTSIDE LET *)
    (* GEN BEGIN TAG OUTSIDE LET *) val install = install (* GEN END TAG OUTSIDE LET *)
    (* GEN BEGIN TAG OUTSIDE LET *) val uninstall = uninstall (* GEN END TAG OUTSIDE LET *)
    (* GEN BEGIN TAG OUTSIDE LET *) val installROrder = installROrder (* GEN END TAG OUTSIDE LET *)
    (* GEN BEGIN TAG OUTSIDE LET *) val uninstallROrder = uninstallROrder (* GEN END TAG OUTSIDE LET *)
    (* GEN BEGIN TAG OUTSIDE LET *) val selLookup = selLookup (* GEN END TAG OUTSIDE LET *)
    (* GEN BEGIN TAG OUTSIDE LET *) val selLookupROrder = selLookupROrder (* GEN END TAG OUTSIDE LET *)
    (* GEN BEGIN TAG OUTSIDE LET *) val mutLookup = mutLookup (* GEN END TAG OUTSIDE LET *)
    (* GEN BEGIN TAG OUTSIDE LET *) val closure = (* GEN BEGIN FUNCTION EXPRESSION *) fn a => closure ([a], nil) (* GEN END FUNCTION EXPRESSION *) (* GEN END TAG OUTSIDE LET *)
  end (* local *)
end (* GEN END FUNCTOR DECL *); (* functor Order *)
