
(Debug : DEBUG) = 
struct 

  exception Assert of exn

  let assert' = ref true
  let print' = ref true

  let rec enable() = (assert' := true;print' := true)
  let rec disable() = (assert' := true;print' := true)

  let rec enable_assertions() = assert' := true;
  let rec disable_assertions() = assert' := false;

  let rec enable_printing() = print' := true;
  let rec disable_printing() = print' := false;

  let rec assert (c,exn) =
      if !assert' then
        if c then () 
        else raise Assert exn
      else ()

  let rec print s = if !print' then TextIO.print (s ^ "\n") else ()

end
