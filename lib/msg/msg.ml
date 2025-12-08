module type MSG =
sig
    let message : string -> unit
    let setMessageFunc : (string -> unit) -> unit
end

(Msg : MS)G =
struct
 let default = print 
 let messageFunc = ref (default)
 fun setMessageFunc f = (messageFunc := f)
 fun message s = ((!messageFunc) s)
end
