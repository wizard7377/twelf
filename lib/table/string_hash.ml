(* String Hash Table *)
(* Author: Frank Pfenning *)

(StringHash : STRING_HASH) =
struct
  let rec stringHash (s) =
      (* sample 4 characters from string *)
      let
	let rec num (i) = Char.ord (String.sub (s,i)) mod 128
	let n = String.size (s)
      in
	if n = 0 then 0
	else let
	       let a = n-1
	       let b = n div 2
	       let c = b div 2
	       let d = b + c
	     in
	       num(a)+128*(num(b)+128*(num(c)+128*num(d)))
	     end
      end
end;; (* module StringHash *)
