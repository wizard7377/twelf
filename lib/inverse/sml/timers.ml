
(Timers : TIMERS) =
struct

  let centers : Timing.center list ref = ref []

  let rec add_timer name =
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

  let rec reset () = List.app Timing.reset (!centers)

  let rec check () =
      (List.app (print o Timing.toString) (!centers);
       print (Timing.sumToString total))

  let rec show () = (check (); reset ()) 

end
