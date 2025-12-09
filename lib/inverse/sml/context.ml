
(Context : CONTEXT) =
struct 

  module L = Lib

  type 'a ctx = 'a list
  exception Context of string
                      
  let empty = []

  let rec lookup(l,n) = 
      SOME (L.ith n l) handle Fail _ => NONE

  let rec push (ctx,p) = p::ctx

  let rec list l = l

end
