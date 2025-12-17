Constraints  Conv CONV     CONSTRAINTS  struct (*! structure IntSyn = IntSyn' !*)
exception (*
     Constraints cnstr are of the form (X<I>[s] = U).
     Invariants:
       G |- s : G'  G' |- X<I> : V
       G |- U : W
       G |- V[s] == W : L
       (X<>,s) is whnf, but X<>[s] is not a pattern
     If X<I> is uninstantiated, the constraint is inactive.
     If X<I> is instantiated, the constraint is active.

     Constraints are attached directly to the EVar X
     or to a descendent  -fp?
  *)
module (* simplify cnstrs = cnstrs'
       Effects: simplifies the constraints in cnstrs by removing constraints
         of the form U = U' where G |- U == U' : V (mod beta/eta)
         Neither U nor U' needs to be a pattern
         *)
let rec simplifynil nil simplify((ref solved) :: cnstrs) simplify cnstrs simplify((eqn as ref (eqn (g,  , u1,  , u2))) :: cnstrs) if conv ((u1,  , id),  , (u2,  , id)) then simplify cnstrs else eqn :: (simplify cnstrs) simplify((fgnCnstr as ref (fgnCnstr csfc)) :: cnstrs) if apply csfc () then simplify cnstrs else fgnCnstr :: (simplify cnstrs)let rec namesToString(name :: nil) name ^ "." namesToString(name :: names) name ^ ", " ^ namesToString nameslet rec warnConstraints(nil) () warnConstraints(names) print ("Constraints remain on " ^ namesToString names ^ "\n")let  inlet  inlet  inend