(* Printer for Compiled Syntax *)
(* Author: Iliano Cervesato *)

functor (* GEN BEGIN FUNCTOR DECL *) CPrint ((*! structure IntSyn' : INTSYN !*)
                (*! structure CompSyn' : COMPSYN !*)
                (*! sharing CompSyn'.IntSyn = IntSyn' !*)
                structure Print: PRINT
                (*! sharing Print.IntSyn = IntSyn' !*)
                structure Formatter : FORMATTER
                  sharing Print.Formatter = Formatter
                structure Names: NAMES
                (*! sharing Names.IntSyn = IntSyn' !*)
                  )
  : CPRINT =
struct

  (*! structure IntSyn = IntSyn' !*)
  (*! structure CompSyn = CompSyn' !*)

  local
    open CompSyn
  in

    fun (* GEN BEGIN FUN FIRST *) compose(IntSyn.Null, G) = G (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) compose(IntSyn.Decl(G, D), G') = IntSyn.Decl(compose(G, G'), D) (* GEN END FUN BRANCH *)

    (* goalToString (G, g) where G |- g  goal *)
    fun (* GEN BEGIN FUN FIRST *) goalToString t (G, Atom(p)) =
         t ^ "SOLVE   " ^ Print.expToString (G, p) ^ "\n" (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) goalToString t (G, Impl (p,A,_,g)) =
         t ^ "ASSUME  " ^ Print.expToString (G, A) ^ "\n" ^
         (clauseToString (t ^ "\t") (G, p)) ^
         goalToString t (IntSyn.Decl(G, IntSyn.Dec(NONE, A)), g) ^ "\n" (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) goalToString t (G, All(D,g)) =
         let
           (* GEN BEGIN TAG OUTSIDE LET *) val D' = Names.decLUName (G, D) (* GEN END TAG OUTSIDE LET *)
         in
           t ^ "ALL     " ^
           Formatter.makestring_fmt (Print.formatDec (G, D')) ^ "\n" ^
           goalToString t (IntSyn.Decl (G, D'), g) ^ "\n"
         end (* GEN END FUN BRANCH *)

    (* auxToString (G, r) where G |- r auxgoal *)
    and (* GEN BEGIN FUN FIRST *) auxToString t (G, Trivial) = "" (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) auxToString t (G, UnifyEq(G', p1, N, ga)) =
         t ^ "UNIFYEqn  " ^ Print.expToString (compose(G',G), p1) ^ " = " ^
                       Print.expToString (compose(G',G), N) ^ "\n" ^
         auxToString t (G, ga) (* GEN END FUN BRANCH *)

    (* clauseToString (G, r) where G |- r  resgoal *)
    and (* GEN BEGIN FUN FIRST *) clauseToString t (G, Eq(p)) =
         t ^ "UNIFY   " ^ Print.expToString (G, p) ^ "\n" (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) clauseToString t (G, Assign(p, ga)) =
         (t ^ "ASSIGN  " ^ (Print.expToString (G, p)  handle _ => "<exc>")
         ^ "\n" ^ (auxToString t (G, ga))) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) clauseToString t (G, And(r, A, g)) =
         clauseToString t (IntSyn.Decl(G, IntSyn.Dec(NONE, A)), r) ^
         goalToString t (G, g) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) clauseToString t (G, In(r, A, g)) =
         let
           (* GEN BEGIN TAG OUTSIDE LET *) val D = Names.decEName (G, IntSyn.Dec (NONE, A)) (* GEN END TAG OUTSIDE LET *)
         in
           clauseToString t (IntSyn.Decl(G, D), r) ^
           t ^ "META    " ^ Print.decToString (G, D) ^ "\n" ^
           goalToString t (G, g)
         end (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) clauseToString t (G, Exists(D, r)) =
         let
           (* GEN BEGIN TAG OUTSIDE LET *) val D' = Names.decEName (G, D) (* GEN END TAG OUTSIDE LET *)
         in
           t ^ "EXISTS  " ^
           (Print.decToString (G, D') handle _ => "<exc>") ^ "\n" ^
           clauseToString t (IntSyn.Decl(G, D'), r)
         end (* GEN END FUN BRANCH *)

      | (* GEN BEGIN FUN BRANCH *) clauseToString t (G, Axists(D as IntSyn.ADec(SOME(n), d), r)) =
         let
           (* GEN BEGIN TAG OUTSIDE LET *) val D' = Names.decEName (G, D) (* GEN END TAG OUTSIDE LET *)
         in
           t ^ "EXISTS'  " ^
           (Print.decToString (G, D') handle _ => "<exc>") ^ "\n" ^
           clauseToString t (IntSyn.Decl(G, D'), r)
         end (* GEN END FUN BRANCH *)

    fun (* GEN BEGIN FUN FIRST *) subgoalsToString t (G, True) = t ^ "True " (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) subgoalsToString t (G, Conjunct(Goal, A, Sg)) =
        t  ^ goalToString t (IntSyn.Decl(G,IntSyn.Dec(NONE, A)), Goal) ^ " and " ^ subgoalsToString t (G, Sg) (* GEN END FUN BRANCH *)

    (* conDecToString (c, clause) printed representation of static clause *)
    fun (* GEN BEGIN FUN FIRST *) conDecToString (c, SClause(r)) =
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val _ = Names.varReset IntSyn.Null (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val name = IntSyn.conDecName (IntSyn.sgnLookup c) (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val l = String.size name (* GEN END TAG OUTSIDE LET *)
        in
          name ^ (if l > 6 then ":\n" else ":") ^
          (clauseToString "\t" (IntSyn.Null, r) ^ "\n")
        end (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) conDecToString (c, Void) =
          Print.conDecToString (IntSyn.sgnLookup c) ^ "\n\n" (* GEN END FUN BRANCH *)

    (* sProgToString () = printed representation of static program *)
    fun sProgToString () =
        let (* GEN BEGIN TAG OUTSIDE LET *) val (size, _) = IntSyn.sgnSize () (* GEN END TAG OUTSIDE LET *)
            fun ts (cid) = if cid < size
                             then conDecToString (cid, CompSyn.sProgLookup cid)
                                  ^ ts (cid+1)
                           else ""
         in
           ts 0
         end

    (* dProgToString (G, dProg) = printed representation of dynamic program *)
    fun (* GEN BEGIN FUN FIRST *) dProgToString (DProg (IntSyn.Null, IntSyn.Null)) = "" (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) dProgToString (DProg (IntSyn.Decl(G,IntSyn.Dec(SOME x,_)),
                       IntSyn.Decl(dPool, CompSyn.Dec (r,_,_)))) =
          dProgToString (DProg (G,dPool))
          ^ "\nClause    " ^ x ^ ":\n"
          ^ clauseToString "\t" (G, r) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) dProgToString (DProg (IntSyn.Decl(G, IntSyn.Dec(SOME x,A)),
                       IntSyn.Decl(dPool, CompSyn.Parameter))) =
         dProgToString (DProg (G, dPool))
         ^ "\nParameter " ^ x ^ ":\t"
         ^ Print.expToString (G, A) (* GEN END FUN BRANCH *)
     (* case for CompSyn.BDec is still missing *)



  end  (* local open ... *)

end (* GEN END FUNCTOR DECL *); (* functor CPrint *)
