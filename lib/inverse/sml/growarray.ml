
(GrowArray : GROWARRAY) =
struct

  module A = Array

  type 'a growarray = (int * ('a option) A.array) ref

  (* start with 16 cells, why not? *)
  let rec empty () = ref (0, A.array(16, NONE))

  let rec growarray n i = ref (n, (A.array(n, SOME i)))

  let rec sub (ref (used, a)) n =
    if n < used andalso n >= 0
    then (case A.sub(a, n) of
            NONE => raise Subscript
          | SOME z => z)
    else raise Subscript

  let rec length (ref (l, _)) = l

  (* grow to accomodate at least n elements *)
  let rec accomodate (r as ref(l, a)) n =
      if A.length a >= (n + 1) then ()
      else
        let 
          let rec nextpower x = 
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

  let rec update r n x =
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

  let rec append (r as ref(n, _)) x =
    let
      let _ = accomodate r (n + 1)
      let (_, a) = !r
    in
      A.update(a, n, SOME x);
      r := (n + 1, a)
    end

  let rec used arr n = 
      (ignore (sub arr n); true) 
      handle Subscript => false

  let rec finalize (ref (n, a)) =
    A.tabulate (n, (fun x -> case A.sub(a, x) of
                                   NONE => raise Subscript
                                 | SOME z => z))

end
