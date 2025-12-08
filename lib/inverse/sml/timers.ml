
(Timers : TIMER)S =
struct

  let centers : Timing.center list ref = ref []

  fun add_timer name =
      let
        let center = Timing.newCenter name
      in
        centers := !centers @ [center];
        center
      end

  let checking    = add_timer ("Checking      ")
  let eta_normal  = add_timer ("Eta Normal    ")
  let printing    = add_timer ("Printing      ")
  let translation = add_timer ("Translation   ")

  let total    = Timing.sumCenter ("Total         ", !centers)

  let time = Timing.time

  fun reset () = List.app Timing.reset (!centers)

  fun check () =
      (List.app (print o Timing.toString) (!centers);
       print (Timing.sumToString total))

  fun show () = (check (); reset ()) 

end
