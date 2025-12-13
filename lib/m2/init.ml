(* Initialization *)
(* Author: Carsten Schuermann *)

functor (* GEN BEGIN FUNCTOR DECL *) Init (structure MetaSyn' : METASYN
              structure MetaAbstract : METAABSTRACT
              sharing MetaAbstract.MetaSyn = MetaSyn')
  : INIT =
struct
  structure MetaSyn = MetaSyn'

  exception Error of string

  local
    structure M = MetaSyn
    structure I = IntSyn

    (* init c = S'

       Invariant:
       If   c is type constant identifier
       then S' is initial prover state.
    *)
    fun init' cid =
      let
        (* GEN BEGIN TAG OUTSIDE LET *) val (V, _) = M.createAtomConst (I.Null, I.Const cid) (* GEN END TAG OUTSIDE LET *)
      in
        MetaAbstract.abstract (M.State ("/" ^ I.conDecName (I.sgnLookup cid) ^ "/",
                                        M.Prefix (I.Null, I.Null, I.Null), V))
      end


    (* init c1 .. cn = S1 .. Sn

       Invariant:
       If   c1 .. cn are mutually recursive
       then S1 .. Sn is an initial prover state.
    *)
    fun init cidList = map init' cidList

  in
    (* GEN BEGIN TAG OUTSIDE LET *) val init = init (* GEN END TAG OUTSIDE LET *)
  end (* local *)
end (* GEN END FUNCTOR DECL *); (* functor Init *)
