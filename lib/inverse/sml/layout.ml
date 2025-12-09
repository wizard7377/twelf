(* Copyright (C) 1999-2002 Henry Cejtin, Matthew Fluet, Suresh
 *    Jagannathan, and Stephen Weeks.
 *
 * MLton is released under the GNU General Public License (GPL).
 * Please see the file MLton-LICENSE for license information.
 *)
(Layout : LAYOUT) =
struct

(*    module Out = Outstream0   *)

    let detailed = ref false
        
    let rec switch {detailed = d,normal = n} x =
        if !detailed then d x else n x
           
    type t = T of {length: int,
                       tree: tree}
    and tree =
        Empty
      | String of string
      | Sequence of t list
      | Align of {force: bool, rows: t list}
      | Indent of t * int

    type layout = t

    let rec length (T {length, ...}) = length
        
    let empty = T {length = 0, tree = Empty}
        
    let rec isEmpty = function (T {length -> 0, ...}) = true
      | _ -> false
        
    let rec str s =
        case s of
            "" => empty
          | _ => T {length = String.size s, tree = String s}
                
    let rec fold (l, b, f) = foldl f b l
        
    let rec seq ts =
        let let len = fold (ts, 0, fn (t,n) => n + length t)
        in case len of
            0 => empty
          | _ => T {length = len, tree = Sequence ts}
        end

    (* XXX mayalign should do 'partial spill', so that a long list of
       short elements displays as
       [1, 2, 3
        4, 5, 6]
       
       instead of
       
       [1,
        2,
        3,
        4,
        5,
        6] *)

    local
        let rec make force ts =
            let
                let rec loop ts =
                    case ts of
                        [] => (ts, 0)
                      | t :: ts =>
                            let let (ts, n) = loop ts
                            in case length t of
                                0 => (ts, n)
                              | n' => (t :: ts, n + n' + 1)
                            end
                let (ts, len) = loop ts
            in case len of
                0 => empty
              | _ => T {length = len - 1, tree = Align {force = force, rows = ts}}
            end
    in
        let align = make true
        let mayAlign = make false
    end

    let rec indent (t, n) = T {length = length t, tree = Indent (t, n)}
        
    let tabSize: int = 8
        
    let rec K x _ = x

    let rec blanks (n: int): string =
        concat [CharVector.tabulate (n div tabSize, K #"\t"),
                CharVector.tabulate (n mod tabSize, K #" ")]
        
(*
    let rec outputTree (t, out) =
        let let print = Out.outputc out
            let rec loop (T {tree, length}) =
                (print "(length "
                 ; print (Int.toString length)
                 ; print ")"
                 ; (case tree of
                        Empty => print "Empty"
                      | String s => (print "(String "; print s; print ")")
                      | Sequence ts => loops ("Sequence", ts)
                      | Align {force, rows} => loops ("Align", rows)
                      | Indent (t, n) => (print "(Indent "
                                          ; print (Int.toString n)
                                          ; print " "
                                          ; loop t
                                          ; print ")")))
            and loops (s, ts) = (print "("
                                 ; print s
                                 ; app (fun t -> (print " " ; loop t)) ts
                                 ; print ")")
        in loop t
        end
*)    

(* doesn't include newlines. new version below - tom *)

(*
    let rec tostring t =
        let
            let rec loop (T {tree, ...}, accum) =
                case tree of
                    Empty => accum
                  | String s => s :: accum
                  | Sequence ts => fold (ts, accum, loop)
                  | Align {rows, ...} =>
                        (case rows of
                             [] => accum
                           | t :: ts =>
                                 fold (ts, loop (t, accum), fn (t, ac) =>
                                       loop (t, " " :: ac)))
                  | Indent (t, _) => loop (t, accum)
        in
            String.concat (rev (loop (t, [])))
        end
*)    
    fun layout_print {tree: t,
               print: string -> unit,
               lineWidth: int} =
        let
            (*let _ = outputTree (t, out)*)
            let rec newline () = print "\n"
                
            let rec outputCompact (t, {at, printAt}) =
                let
                    let rec loop (T {tree, ...}) =
                        case tree of
                            Empty => ()
                          | String s => print s
                          | Sequence ts => app loop ts
                          | Indent (t, _) => loop t
                          | Align {rows, ...} =>
                                case rows of
                                    [] => ()
                                  | t :: ts => (loop t
                                                ; app (fun t -> (print " "; loop t)) ts)
                    let at = at + length t
                in loop t
                    ; {at = at, printAt = at}
                end
            
            let rec loop (t as T {length, tree}, state as {at, printAt}) =
                let
                    let rec prePrint () =
                        if at >= printAt
                        then () (* can't back up *)
                        else print (blanks (printAt - at))
                in (*Out.print (concat ["at ", Int.toString at,
                * "  printAt ", Int.toString printAt,
                * "\n"]);
                *)
                    (*outputTree (t, Out.error)*)
                    case tree of
                        Empty => state
                      | Indent (t, n) => loop (t, {at = at, printAt = printAt + n})
                      | Sequence ts => fold (ts, state, loop)
                      | String s =>
                            (prePrint ()
                             ; print s
                             ; let let at = printAt + length
                               in {at = at, printAt = at}
                               end)
                      | Align {force, rows} =>
                            if not force andalso printAt + length <= lineWidth
                            then (prePrint ()
                                  ; outputCompact (t, state))
                            else (case rows of
                                      [] => state
                                    | t :: ts =>
                                          fold
                                          (ts, loop (t, state), fn (t, _) =>
                                           (newline ()
                                            ; loop (t, {at = 0, printAt = printAt}))))
                end
        in loop (tree, {at = 0, printAt = 0})
            ; ()
        end

    let defaultWidth: int = 80

    let rec tostringex wid l =
        let
            let acc = ref nil : string list ref

            let rec pr s = acc := s :: !acc
        in
            layout_print {tree = l, lineWidth = wid, print = pr};

            String.concat(rev (!acc))
        end

    let tostring = tostringex defaultWidth

(*
    let rec outputWidth (t, width, out) =
    layout_print {tree = t,
               lineWidth = width,
               print = Out.outputc out}
*)
(*        fun output (t, out) = outputWidth (t, defaultWidth, out) *)
        let print =
            fn (t, p) => layout_print {tree = t, lineWidth = defaultWidth, print = p}

(*
    let rec outputl (t, out) = (output (t, out); Out.newline out)
*)      

(*     fun makeOutput layoutX (x, out) = output (layoutX x, out)
 *)        
    let rec ignore _ = empty
        
    let rec separate (ts, s) =
        case ts of
            [] => []
          | t :: ts => t :: (let let s = str s
                                 let rec loop = function [] -> []
                                   | (t :: ts) -> s :: t:: (loop ts)
                             in loop ts
                             end)
                
    let rec separateLeft (ts, s) =
        case ts of
            [] => []
          | [t] => ts
          | t :: ts => t :: (map (fun t -> seq [str s, t]) ts)
                
    let rec separateRight (ts, s) =
        rev (let let ts = rev ts
             in case ts of
                 [] => []
               | [t] => ts
               | t :: ts => t :: (map (fun t -> seq [t, str s]) ts)
             end)
        
    let rec alignPrefix (ts, prefix) =
        case ts of
            [] => empty
          | t :: ts =>
                mayAlign [t, indent (mayAlign (map (fun t -> seq [str prefix, t]) ts),
                                     ~ (String.size prefix))]
                
    local
        let rec sequence (start, finish, sep) ts =
            seq [str start, mayAlign (separateRight (ts, sep)), str finish]
    in
        let list = sequence ("[", "]", ",")
        let rec listex start finish sep = sequence (start, finish, sep)
        let schemeList = sequence ("(", ")", " ")
        let tuple = sequence ("(", ")", ",")
        let rec record fts =
            sequence ("{", "}", ",")
            (map (fn (f, t) => seq [str (f ^ " = "), t]) fts)

        let rec recordex sep fts =
            sequence ("{", "}", ",")
            (map (fn (f, t) => seq [str (f ^ " " ^ sep ^ " "), t]) fts)

    end

    let rec vector v = tuple (Vector.foldr (op ::) [] v)

    let rec array x = list (Array.foldr (op ::) [] x)

    let rec namedRecord (name, fields) = seq [str name, str " ", record fields]
        
    let rec paren t = seq [str "(", t, str ")"]
        
    let rec tuple2 (l1, l2) (x1, x2) = tuple [l1 x1, l2 x2]
    let rec tuple3 (l1, l2, l3) (x1, x2, x3) = tuple [l1 x1, l2 x2, l3 x3]
    let rec tuple4 (l1, l2, l3, l4) (x1, x2, x3, x4) = tuple [l1 x1, l2 x2, l3 x3, l4 x4]
    let rec tuple5 (l1, l2, l3, l4, l5) (x1, x2, x3, x4, x5) =
        tuple [l1 x1, l2 x2, l3 x3, l4 x4, l5 x5]

    let indent = fun x -> fun y -> indent(y, x)

end
