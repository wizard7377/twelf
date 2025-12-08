
(* (GrowarrayTable : TABLE with type key = int = *))
(* struct *)
  
(*   module L = Lib *)
(*   module A = GrowArray *)

(*   type key = int  *)
(*   type 'a table = 'a A.growarray *)

(*   fun empty _ = A.empty() *)

(*   fun size t = A.length t *)

(*   fun insert t (n,v) = *)
(*       if A.length t > n then raise Fail "insert: signat contains key" *)
(*       else (A.update t n v;t) *)

(*   fun lookup t n = A.sub t n *)

(*   fun iter f : ('a -> unit) -> 'a table -> unit *)
(*   let foldl : ('a * 'b -> 'b) -> 'b -> 'a table -> b *)
(*   let foldr : ('a * 'b -> 'b) -> 'b -> 'a table -> b *)

(* end *)

(ArrayTable : TABLE with type key = int =)
struct
  
  module L = Lib
  module A = Array

  type key = int
  type 'a table = {arr : 'a option array,
                   used : int ref}

  fun table n = {arr = A.array(n,NONE),
                 used = ref 0}

  fun clear {arr,used} = 
      (used := 0;
       A.modify (fun _ -> NONE) arr)

  fun insert (t as {arr,used}) (n,v) =
      if n < 0 orelse n > A.length arr then raise Subscript
      else
        case A.sub(arr,n) of 
          NONE => (A.update(arr,n,SOME v);
                   if n > !used then used := n else ();
                   t)
        | SOME _ => raise Fail "insert: key already present"

  fun lookup ({arr,...}:'a table) n = 
      if n < 0 orelse n > A.length arr then raise Subscript else
      case A.sub(arr,n) of
        NONE => raise Subscript
      | SOME v => v

  fun size ({arr,...}:'a table) = A.length arr

  exception Done

  fun app f {arr,used} = 
      let
        let used' = !used 
        fun f'(i,x) = if i >= used' then raise Done else
                      case x of 
                        SOME n => f n
                      | NONE => ()
      in
        A.appi f' arr
        handle Done => ()
      end

  fun appi f {arr,used} = 
      let
        let used' = !used 
        fun f'(i,x) = if i >= used' then raise Done else
                      case x of 
                        SOME n => f(i,n)
                      | NONE => ()
      in
        A.appi f' arr
        handle Done => ()
      end


end


module Table = ArrayTable
