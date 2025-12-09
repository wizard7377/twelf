
(Translate : TRANSLATE) =
struct 

  module L = Lib
  module I = IntSyn
  module S = Syntax
  module Sig = S.Signat
  module C = ClausePrint
  module D = Debug

  (* -------------------------------------------------------------------------- *)
  (*  Exceptions                                                                *)
  (* -------------------------------------------------------------------------- *)

  exception Translate of string
  exception Trans1 of S.const * I.ConDec
  exception Fail_exp of string * I.Exp

  (* -------------------------------------------------------------------------- *)
  (*  Basic Translation                                                         *)
  (* -------------------------------------------------------------------------- *)

  let rec translate_uni = function I.Kind -> S.Kind 
    | I.Type -> S.Type

  let rec translate_head = function (I.BVar i) -> S.BVar i
    | (I.Const c) -> S.Const c
    | (I.Def c) -> S.Const c
    | _ -> raise Translate "translate_head: bad case"

  let rec translate_depend = function I.No -> S.No
    | I.Maybe -> S.Maybe
    | _ -> raise Fail "translate_depend: bad case"

  and translate_exp (I.Uni uni) = S.Uni (translate_uni uni)
    | translate_exp (I.Pi((I.Dec(name,U1),depend),U2)) = 
      S.Pi {var = name,
            arg = translate_exp U1,
            depend = translate_depend depend,
            body = translate_exp U2}
    | translate_exp (I.Root(H,S)) =
      S.Root(translate_head H,translate_spine S)
    | translate_exp (I.Lam(I.Dec(name,_),U)) =
      S.Lam {var = name,
             body = translate_exp U}
    | translate_exp E = raise Fail_exp("translate_exp: bad case",E)

  and translate_spine I.Nil = S.Nil
    | translate_spine (I.App(U,S)) = 
      S.App(translate_exp U,translate_spine S)
    | translate_spine _ = raise Translate "translate_spine: bad case"

  let rec translate_condec = function (cid,I.ConDec(name,_,_,_,E,U)) -> 
      S.Decl {id = cid,
              name = name,
              exp = translate_exp E,
              uni = translate_uni U}
    | (cid,I.ConDef(name,_,_,U,V,I.Type,I.Anc(ex1,h,exa))) -> 
      S.Def {id = cid,
             name = name,
             exp = translate_exp V,
             def = translate_exp U,
             height=h,
             root = L.the exa,
             uni = S.Type}
    | (cid,I.AbbrevDef(name,mid,n,U,V,lev)) -> 
      S.Abbrev {id = cid,
                name = name,
                exp = translate_exp V,
                def = translate_exp U,
                uni = translate_uni lev}
    | cdec -> raise Trans1 cdec
(*     | translate_condec _ = raise Translate "translate_condec: bad case" *)

  let rec can_translate = function (I.ConDec _) -> true
    | (I.ConDef _) -> true
    | (I.AbbrevDef _) -> true
    | _ -> false

  let rec translate_signat'() = 
      let
        let n = L.fst (IntSyn.sgnSize()) 
        let ns = L.upto(0,n-1)
        let cds = map IntSyn.sgnLookup ns
        let cds' = L.filter (fn (id,dec) => can_translate dec) (L.zip ns cds)
      in
        map (fn (dec as (c,e)) => (c,translate_condec dec)) cds'
      end

  let rec translate_signat() = (Timers.time Timers.translation translate_signat') ()

end

