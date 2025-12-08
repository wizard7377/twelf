
module GrowArray : GROWARRAY =
struct

  module A = Array

  type 'a growarray = (int * ('a option) A.array) ref

  (* start with 16 cells, why not? *)
  fun empty () = ref (0, A.array(16, NONE))

  fun growarray n i = ref (n, (A.array(n, SOME i)))

  fun sub (ref (used, a)) n =
    if n < used andalso n >= 0
    then (case A.sub(a, n) of
            NONE => raise Subscript
          | SOME z => z)
    else raise Subscript

  fun length (ref (l, _)) = l

  (* grow to accomodate at least n elements *)
  fun accomodate (r as ref(l, a)) n =
      if A.length a >= (n + 1) then ()
      else
        let 
          fun nextpower x = 
              if x >= (n + 1) 
              then x
              else nextpower (x * 2)
          let ns = nextpower (A.length a)
          let na = A.tabulate(ns,
                              (fun i ->
                                  if i < l
                                  then A.sub(a, i)
                                  else NONE))
        in
          r := (l, na)
        end

  fun update r n x =
    if n < 0 then raise Subscript
    else
      let 
        let _ = accomodate r n
        let (l, a) = !r
      in
        A.update(a, n, SOME x);
        (* also update 'used' *)
        if n >= l
        then r := (n + 1, a)
        else ()
      end

  fun append (r as ref(n, _)) x =
    let
      let _ = accomodate r (n + 1)
      let (_, a) = !r
    in
      A.update(a, n, SOME x);
      r := (n + 1, a)
    end

  fun used arr n = 
      (ignore (sub arr n); true) 
      handle Subscript => false

  fun finalize (ref (n, a)) =
    A.tabulate (n, (fun x -> case A.sub(a, x) of
                                   NONE => raise Subscript
                                 | SOME z => z))

end
