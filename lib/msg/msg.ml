module type MSG =
sig
    let message : string -> unit
    let setMessageFunc : (string -> unit) -> unit
end

(Msg : MSG) =
struct
 let default = print 
 let messageFunc = ref (default)
 let rec setMessageFunc f = (messageFunc := f)
 let rec message s = ((!messageFunc) s)
end
