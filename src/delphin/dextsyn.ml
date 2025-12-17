DextSyn  ExtSyn' EXTSYN    Parsing' PARSING     DEXTSYN  struct (*  structure Stream = Stream' *)
module module (*  structure Paths = ExtSyn.Paths
  structure Lexer = Lexer' *)
module (*  structure S = Parsing'.Lexer.Stream *)
module type Ast Decs CreateDecl FormDecl FunDecl ValDecl Cases World Form(* | Arrow of Form * Form *)
(* | WldDef of (string list) * Form *)
 Prog(* | Rec of MDec * Prog *)
 Head Pat MDec Block(* and Term
  = Term of string
*)
 Term Dec(*
fun parseLFDecs (Ast dl) =
  let val tf = OS.FileSys.tmpName ()
      val tos = TextIO.openOut tf
      fun parseLFDecs' [] = ()
       |  parseLFDecs' ((LFConDec ld) ::ds) =
           (TextIO.output(tos, ld);
           parseLFDecs' ds)
       |  parseLFDecs' (_ ::ds) = parseLFDecs' ds
      val _ = parseLFDecs' dl
      val _ = TextIO.closeOut tos
      val _ = Twelf.loadFile tf
      val _ = OS.FileSys.remove tf
  in ()
  end

*)
(*

fun rulesToCase (Ast decs) =
   let
      fun rulesToCase' [] = []
      |   rulesToCase' (ProgDec (Head (s,pts), prg) :: ds) =
            let val cds = rulesToCase' ds
            in
               case cds of
                  ProgDec (Head (s',_), Case ps) ::ds'' =>
                     if s = s'
                     then ProgDec (Head (s, []), Case ((pts,prg)::ps))::ds''
                     else
                         ProgDec (Head (s,[]), Case [(pts,prg)]):: cds
                | _ => ProgDec (Head (s,[]), Case [(pts,prg)]):: cds
             end
      |   rulesToCase' (d::ds) =
             let val cds = rulesToCase' ds
             in
                (d::cds)
             end

   in
      Ast (rulesToCase' decs)
   end


 (* Invariant:  all programs in ast have been put in case form *)
  fun abstractProgs' [] = []
    | abstractProgs' (ProgDec (Head (nm,e), cp)::ds) =
         ProgDec (Head (nm,e), Rec (MDec (nm, NONE), cp))::
                 (abstractProgs' ds)
    | abstractProgs' (d::ds) = (d::(abstractProgs' ds))


 fun abstractProgs ast =
      let
          val ast' = rulesToCase ast
          val (Ast decs) = ast'
          val decs' = abstractProgs' decs
      in (Ast decs')
      end

*)
(*     val appendPats = appendPats
     val parseLFDecs = parseLFDecs
     val abstractProgs = abstractProgs
*)
end