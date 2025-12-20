(* Compatibility shim from Basis-current ArraySlice to Basis-97 Array *)


(* Author: Christopher Richards *)


module ArraySlice : ARRAY_SLICE = struct type 'a slice = 'a Array.array * int * int option
let rec slice s  = s
let appi = Array.appi
 end

