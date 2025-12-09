
module type SIGNAT =
sig
  type key
  type 'a sgn
  exception Signat of string
  let empty : unit -> 'a sgn
  let insert : 'a sgn -> key * 'a -> 'a sgn (* raises Signat if key is not fresh*)
  let lookup : 'a sgn -> key -> 'a (* raises Signat if not present *)
  let size : 'a sgn -> int
end

(ListSignat : SIGNAT with type key = int =)
struct 

  module L = Lib
  type key = int
  type 'a sgn = (key * 'a) list

  exception Signat of string
                      
  let rec empty() = []

  let rec insert sgn (p as (k,a)) = 
      if L.exists (fn (k',_) => k = k') sgn
      then raise Signat "insert: signat contains key"
      else p::sgn

  let rec lookup sgn x = 
      case L.assoc x sgn of 
        SOME y => y
      | NONE => raise Signat "lookup: no such key"

  let rec size l = length l

end

(GrowarraySignat : SIGNAT with type key = int =)
struct
  
  module L = Lib
  module G = GrowArray

  type key = int
  type 'a sgn = {arr : 'a G.growarray,
                 size : int ref}

  exception Signat of string
                      
  let size = ref 0

  let rec empty() = {arr = G.empty(),
                 size = ref 0}

  let rec insert (sgn:('a sgn)) (n,v) =
      if G.length (#arr sgn) > n
      then raise Signat "insert: signat contains key"
      else
        (G.update (#arr sgn) n v;
         (if n > !(#size sgn) then (#size sgn) := n else ());
         sgn)

  let rec lookup (sgn:'a sgn) n = G.sub (#arr sgn) n

  let rec size (sgn:'a sgn) = !(#size sgn)

end

module Signat = GrowarraySignat
