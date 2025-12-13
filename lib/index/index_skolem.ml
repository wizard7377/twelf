(* Indexing (Constants and Skolem constants) *)
(* Author: Carsten Schuermann *)
(* Modified: Frank Pfenning *)

functor (* GEN BEGIN FUNCTOR DECL *) IndexSkolem (structure Global : GLOBAL
                     structure Queue : QUEUE
                     (*! structure IntSyn' : INTSYN !*)
                       )
  : INDEX =
struct
  (*! structure IntSyn = IntSyn' !*)

  local
    structure I = IntSyn

    fun (* GEN BEGIN FUN FIRST *) cidFromHead (I.Const c) = c (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) cidFromHead (I.Def c) = c (* GEN END FUN BRANCH *)

    (* Index array

       Invariant:
       For all type families  a
       indexArray (a) = c1,...,cn
       where c1,...,cn is a queue consisting of all constants with
       target family a
    *)
    (* GEN BEGIN TAG OUTSIDE LET *) val indexArray : (IntSyn.head Queue.queue) Array.array =
        Array.array (Global.maxCid + 1, Queue.empty) (* GEN END TAG OUTSIDE LET *)

    (* reset () = ()
       Empties index array
    *)
    fun reset () = Array.modify ((* GEN BEGIN FUNCTION EXPRESSION *) fn _ => Queue.empty (* GEN END FUNCTION EXPRESSION *)) indexArray

    (* update (a, c) = ()
       inserts c into the index queue for family a
       Invariant: a = target family of c
    *)
    fun update (a, c) =
        Array.update (indexArray, a,
                      Queue.insert (c, Array.sub (indexArray, a)))

    (* install (c) = ()
       installs c into the correct index queue
       presently ignores definitions
    *)
    fun (* GEN BEGIN FUN FIRST *) install fromCS (H as I.Const c) =
        (case (fromCS, I.sgnLookup (c))
          of (_, I.ConDec (_, _, _, _, A, I.Type)) => update (cidFromHead (I.targetHead A), H)
           | (I.Clause, I.ConDef (_, _, _, _, A, I.Type, _)) => update (cidFromHead (I.targetHead A), I.Def(c))
           | _ => ()) (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) install fromCS (H as I.Skonst c) =
        (case I.sgnLookup (c)
           of I.SkoDec (_, _, _, A, I.Type) => update (cidFromHead (I.targetHead A), H)
            | _ => ()) (* GEN END FUN BRANCH *)

    fun remove (a, cid) =
        (case Queue.deleteEnd (Array.sub (indexArray, a))
           of NONE => ()
            | SOME (I.Const cid', queue') =>
                if cid = cid' then Array.update (indexArray, a, queue')
                else ()
            | SOME (I.Skonst cid', queue') =>
                if cid = cid' then Array.update (indexArray, a, queue')
                else ())

    fun uninstall cid =
        (case I.sgnLookup cid
           of I.ConDec (_, _, _, _, A, I.Type) => remove (cidFromHead (I.targetHead A), cid)
            | I.SkoDec (_, _, _, A, I.Type) => remove (cidFromHead (I.targetHead A), cid)
            | _ => ())

    fun resetFrom mark =
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val (limit, _) = I.sgnSize () (* GEN END TAG OUTSIDE LET *)
          fun iter i = if i < mark then ()
                       else (uninstall i;
                             Array.update (indexArray, i, Queue.empty))
        in
          iter (limit - 1)
        end

    (* lookup a = [c1,...,cn] *)
    (*
       c1,...,cn are all constants with target family a
       in order of declaration, defined constants are omitted.

       A second lookup after the first without intermediate inserts will
       be in constant time.
    *)
    fun lookup a =
        let fun (* GEN BEGIN FUN FIRST *) lk (l, NONE) = l (* GEN END FUN FIRST *)
              | (* GEN BEGIN FUN BRANCH *) lk (l, SOME(q')) =
                (Array.update (indexArray, a, q'); l) (* GEN END FUN BRANCH *)
        in
          lk (Queue.toList (Array.sub (indexArray, a)))
        end

  in

    (* GEN BEGIN TAG OUTSIDE LET *) val reset = reset (* GEN END TAG OUTSIDE LET *)
    (* GEN BEGIN TAG OUTSIDE LET *) val resetFrom = resetFrom (* GEN END TAG OUTSIDE LET *)
    (* GEN BEGIN TAG OUTSIDE LET *) val install = install (* GEN END TAG OUTSIDE LET *)
    (* GEN BEGIN TAG OUTSIDE LET *) val lookup = lookup (* GEN END TAG OUTSIDE LET *)

  end (* local *)

end (* GEN END FUNCTOR DECL *);  (* functor Index *)
