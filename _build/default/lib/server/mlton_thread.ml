(* Construct a 20041109-workalike MLton.Thread for previous MLton versions *)

structure MLton =
struct
  open MLton

  structure Thread =
  struct
    open MLton.Thread
    (* GEN BEGIN TAG INSIDE LET *) fun prepare (f, x) = f (* GEN END TAG INSIDE LET *)
  end

end
