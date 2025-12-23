(* Indexing *)

(* Author: Carsten Schuermann *)

(* Modified: Frank Pfenning *)

module type INDEX = sig
  (*! structure IntSyn : Intsyn.INTSYN !*)
  val reset : unit -> unit
  val resetFrom : IntSyn.cid -> unit
  val install : IntSyn.conDecForm -> IntSyn.head -> unit

  (* lookup a = [c1,...,cn] *)
  (* c1,...,cn are all constants with target family a *)
  (* in order of declaration, defined constants are omitted *)
  val lookup : IntSyn.cid -> IntSyn.head list
end

(* signature INDEX *)
(* Indexing *)

(* Author: Carsten Schuermann *)

(* Modified: Frank Pfenning *)

module Index (Global : Global.GLOBAL) (Queue : Queue.QUEUE) : INDEX = struct
  (*! structure IntSyn = IntSyn' !*)

  module I = IntSyn

  let rec cidFromHead = function I.Const c -> c | I.Def c -> c
  (* Index array

       Invariant:
       For all type families  a
       indexArray (a) = c1,...,cn
       where c1,...,cn is a queue consisting of all constants with
       target family a
    *)

  let indexArray : IntSyn.head Queue.queue Array.array =
    Array.array (Global.maxCid + 1, Queue.empty)
  (* reset () = ()
       Empties index array
    *)

  let rec reset () = Array.modify (fun _ -> Queue.empty) indexArray
  (* update (a, c) = ()
       inserts c into the index queue for_sml family a
       Invariant: a = target family of c
    *)

  let rec update (a, c) =
    Array.update (indexArray, a, Queue.insert (c, Array.sub (indexArray, a)))
  (* install (c) = ()
       installs c into the correct index queue
       presently ignores definitions
    *)

  let rec install fromCS H =
    match (fromCS, I.sgnLookup c) with
    | _, I.ConDec (_, _, _, _, A, I.Type) ->
        update (cidFromHead (I.targetHead A), H)
    | I.Clause, I.ConDef (_, _, _, _, A, I.Type, _) ->
        update (cidFromHead (I.targetHead A), I.Def c)
    | _ -> ()

  let rec remove (a, cid) =
    match Queue.deleteEnd (Array.sub (indexArray, a)) with
    | None -> ()
    | Some (c, queue') ->
        if cid = cid' then Array.update (indexArray, a, queue') else ()

  let rec uninstall cid =
    match I.sgnLookup cid with
    | I.ConDec (_, _, _, _, A, I.Type) ->
        remove (cidFromHead (I.targetHead A), cid)
    | I.ConDef (_, _, _, _, A, I.Type, _) ->
        remove (cidFromHead (I.targetHead A), cid)
    | _ -> ()

  let rec resetFrom mark =
    let limit, _ = I.sgnSize () in
    let rec iter i =
      if i < mark then ()
      else (
        uninstall i;
        Array.update (indexArray, i, Queue.empty))
    in
    iter (limit - 1)
  (* lookup a = [c1,...,cn] *)

  (*
       c1,...,cn are all constants with target family a
       in order of declaration, defined constants are omitted.

       A second lookup after the first without intermediate inserts will
       be in constant time.
    *)

  let rec lookup a =
    let rec lk = function
      | l, None -> l
      | l, Some q' ->
          Array.update (indexArray, a, q');
          l
    in
    lk (Queue.toList (Array.sub (indexArray, a)))

  let reset = reset
  let resetFrom = resetFrom
  let install = install
  let lookup = lookup
  (* local *)
end

(* functor Index *)
