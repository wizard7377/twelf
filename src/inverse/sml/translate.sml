
structure Translate :> TRANSLATE =
struct 

  structure L = Lib
  structure I = IntSyn
  structure S = Syntax
  structure Sig = S.Signat
  structure C = ClausePrint
  structure D = Debug

  (* -------------------------------------------------------------------------- *)
  (*  Exceptions                                                                *)
  (* -------------------------------------------------------------------------- *)

  exception Translate of string
  exception Trans1 of S.const * I.con_dec
  exception Fail_exp of string * I.exp

  (* -------------------------------------------------------------------------- *)
  (*  Basic Translation                                                         *)
  (* -------------------------------------------------------------------------- *)

  fun translate_uni I.Kind = S.Kind 
    | (* GEN CASE BRANCH *) translate_uni I.Type = S.Type

  fun translate_head (I.BVar i) = S.BVar i
    | (* GEN CASE BRANCH *) translate_head (I.Const c) = S.Const c
    | (* GEN CASE BRANCH *) translate_head (I.Def c) = S.Const c
    | (* GEN CASE BRANCH *) translate_head _ = raise Translate "translate_head: bad case"

  fun translate_depend I.No = S.No
    | (* GEN CASE BRANCH *) translate_depend I.Maybe = S.Maybe
    | (* GEN CASE BRANCH *) translate_depend _ = raise Fail "translate_depend: bad case"

  and translate_exp (I.Uni uni) = S.Uni (translate_uni uni)
    | (* GEN CASE BRANCH *) translate_exp (I.Pi((I.Dec(name,U1),depend),U2)) = 
      S.Pi {var = name,
            arg = translate_exp U1,
            depend = translate_depend depend,
            body = translate_exp U2}
    | (* GEN CASE BRANCH *) translate_exp (I.Root(H,S)) =
      S.Root(translate_head H,translate_spine S)
    | (* GEN CASE BRANCH *) translate_exp (I.Lam(I.Dec(name,_),U)) =
      S.Lam {var = name,
             body = translate_exp U}
    | (* GEN CASE BRANCH *) translate_exp E = raise Fail_exp("translate_exp: bad case",E)

  and translate_spine I.Nil = S.Nil
    | (* GEN CASE BRANCH *) translate_spine (I.App(U,S)) = 
      S.App(translate_exp U,translate_spine S)
    | (* GEN CASE BRANCH *) translate_spine _ = raise Translate "translate_spine: bad case"

  fun translate_condec (cid,I.ConDec(name,_,_,_,E,U)) =
      S.Decl {id = cid,
              name = name,
              exp = translate_exp E,
              uni = translate_uni U}
    | (* GEN CASE BRANCH *) translate_condec (cid,I.ConDef(name,_,_,U,V,I.Type,I.Anc(ex1,h,exa))) =
      S.Def {id = cid,
             name = name,
             exp = translate_exp V,
             def = translate_exp U,
             height=h,
             root = L.the exa,
             uni = S.Type}
    | (* GEN CASE BRANCH *) translate_condec (cid,I.AbbrevDef(name,mid,n,U,V,lev)) =
      S.Abbrev {id = cid,
                name = name,
                exp = translate_exp V,
                def = translate_exp U,
                uni = translate_uni lev}
    | (* GEN CASE BRANCH *) translate_condec cdec = raise Trans1 cdec
(*     | translate_condec _ = raise Translate "translate_condec: bad case" *)

  fun can_translate (I.ConDec _) = true
    | (* GEN CASE BRANCH *) can_translate (I.ConDef _) = true
    | (* GEN CASE BRANCH *) can_translate (I.AbbrevDef _) = true
    | (* GEN CASE BRANCH *) can_translate _ = false

  fun translate_signat'() = 
      let
        val n = L.fst (IntSyn.sgnSize()) 
        val ns = L.upto(0,n-1)
        val cds = map IntSyn.sgnLookup ns
        val cds' = L.filter (fn (id,dec) => can_translate dec) (L.zip ns cds)
      in
        map (fn (dec as (c,e)) => (c,translate_condec dec)) cds'
      end

  fun translate_signat() = (Timers.time Timers.translation translate_signat') ()

end

