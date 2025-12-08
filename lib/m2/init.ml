(* Initialization *)
(* Author: Carsten Schuermann *)

module Init (module MetaSyn' : METASYN)
   (module MetaAbstract : METAABSTRACT
              sharing MetaAbstract.MetaSyn = MetaSyn')
  : INIT =
struct
  module MetaSyn = MetaSyn'

  exception Error of string

  local
    module M = MetaSyn
    module I = IntSyn

    (* init c = S'

       Invariant:
       If   c is type constant identifier
       then S' is initial prover state.
    *)
    fun init' cid =
      let
        let (V, _) = M.createAtomConst (I.Null, I.Const cid)
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
    let init = init
  end (* local *)
end;; (* functor Init *)
