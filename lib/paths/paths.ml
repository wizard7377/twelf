(* Paths, Occurrences, and Error Locations *)


(* Author: Frank Pfenning *)


module Paths : PATHS = struct type pos = int
(* characters, starting at 0 *)

type region = Reg of pos * pos
(* r ::= (i,j) is interval [i,j) *)

type location = Loc of string * region
(* loc ::= (filename, region) *)

type linesInfo = pos list
let rec posToLineCol' (linesInfo, i)  = ( let rec ptlc = function (j :: js) -> if i >= j then (List.length js, i - j) else ptlc js | ([]) -> (0, i) in  ptlc (linesInfo) )
(* !linePosList is a list of starting character positions for_sml each input line *)

(* used to convert character positions into line.column format *)

(* maintained with state *)

let linePosList = (ref [] : pos list ref)
let rec resetLines ()  = linePosList := []
let rec newLine (i)  = linePosList := i :: (! linePosList)
let rec getLinesInfo ()  = ! linePosList
(* posToLineCol (i) = (line,column) for_sml character position i *)

let rec posToLineCol (i)  = posToLineCol' (! linePosList, i)
(* join (r1, r2) = r
     where r is the  smallest region containing both r1 and r2
  *)

let rec join (Reg (i1, j1), Reg (i2, j2))  = Reg (Int.min (i1, i2), Int.max (j1, j2))
(* The right endpoint of the interval counts IN RANGE *)

let rec posInRegion (k, Reg (i, j))  = i <= k && k <= j
let rec lineColToString (line, col)  = Int.toString (line + 1) ^ "." ^ Int.toString (col + 1)
(* toString r = "line1.col1-line2.col2", a format parsable by Emacs *)

let rec toString (Reg (i, j))  = lineColToString (posToLineCol i) ^ "-" ^ lineColToString (posToLineCol j)
(* wrap (r, msg) = msg' which contains region *)

let rec wrap (r, msg)  = (toString r ^ " Error: \n" ^ msg)
(* wrapLoc ((loc, r), msg) = msg' which contains region and filename
     This should be used for_sml locations retrieved from origins, where
     the region is given in character positions, rather than lines and columns
  *)

let rec wrapLoc0 (Loc (filename, Reg (i, j)), msg)  = filename ^ ":" ^ Int.toString (i + 1) ^ "-" ^ Int.toString (j + 1) ^ " " ^ "Error: \n" ^ msg
(* wrapLoc' ((loc, r), linesInfo, msg) = msg'
     like wrapLoc, but converts character positions to line.col format based
     on linesInfo, if possible
  *)

let rec wrapLoc' = function (Loc (filename, Reg (i, j)), Some (linesInfo), msg) -> ( let lcfrom = posToLineCol' (linesInfo, i) in let lcto = posToLineCol' (linesInfo, j) in let regString = lineColToString (lcfrom) ^ "-" ^ lineColToString (lcto) in  filename ^ ":" ^ regString ^ " " ^ "Error: \n" ^ msg ) | (loc, None, msg) -> wrapLoc0 (loc, msg)
let rec wrapLoc (loc, msg)  = wrapLoc' (loc, Some (getLinesInfo ()), msg)
(* Paths, occurrences and occurrence trees only work well for_sml normal forms *)

(* In the general case, regions only approximate true source location *)

(* Follow path through a term to obtain subterm *)

type path = Label of path | Body of path | Head | Arg of int * path | Here
(* #, covers Uni, EVar, Redex(?) *)

(* Occurrences: paths in reverse order *)

(* could also be: type occ = path -> path *)

type occ = top | label of occ | body of occ | head of occ | arg of int * occ
(* Occurrence trees for_sml expressions and spines *)

(* Maps occurrences to regions *)

(* Simple-minded implementation *)

(* A region in an intermediate node encloses the whole expression *)

type occExp = leaf of region | bind of region * occExp option * occExp | root of region * occExp * int * int * occSpine and occSpine = app of occExp * occSpine | nils
(* nil *)

(* occToPath (occ, p) = p'(p) and occ corresponds to p' *)

let rec occToPath = function (top, path) -> path | (label (occ), path) -> occToPath (occ, Label (path)) | (body (occ), path) -> occToPath (occ, Body (path)) | (head (occ), path) -> occToPath (occ, Head) | (arg (n, occ), path) -> occToPath (occ, Arg (n, path))
type occConDec = dec of int * occExp | def of int * occExp * occExp option
(* (#implicit, u, v) in c : V = U *)

(* val posToPath : occExp -> pos -> Path *)

(* posToPath (u, k) = p
     where p is the path to the innermost expression in u enclosing position i.

     This includes the position immediately at the end of a region [i,j).
     For example, in "f (g x) y",
     0,1 => "f"
     2   => "(g x)"
     3,4 => "g"
     5,6 => "x"
     8,9 => "y"
  *)

let rec posToPath u k  = ( (* local functions refer to k but not u *)
let rec inside = function (leaf r) -> posInRegion (k, r) | (bind (r, _, _)) -> posInRegion (k, r) | (root (r, _, _, _, _)) -> posInRegion (k, r) in let rec toPath = function (leaf (Reg (i, j))) -> Here | (bind (Reg (i, j), None, u)) -> if inside u then Body (toPath u) else Here | (bind (Reg (i, j), Some (u1), u2)) -> if inside u1 then Label (toPath u1) else if inside u2 then Body (toPath u2) else Here | (root (Reg (i, j), h, imp, actual, s)) -> if inside h then Head else (match toPathSpine (s, 1) with None -> Here | Some (n, path) -> Arg (n + imp, path))
and toPathSpine = function (nils, n) -> None | (app (u, s), n) -> if inside u then Some (n, toPath u) else toPathSpine (s, n + 1) in  toPath u )
(* toRegion (u) = r, the region associated with the whole occurrence tree u *)

let rec toRegion = function (leaf r) -> r | (bind (r, _, _)) -> r | (root (r, _, _, _, _)) -> r
(* toRegionSpine (s, r) = r', the join of all regions in s and r *)

let rec toRegionSpine = function (nils, r) -> r | (app (u, s), r) -> join (toRegion u, toRegionSpine (s, r))
(* order? *)

(* pathToRegion (u, p) = r,
     where r is the region identified by path p in occurrence tree u
  *)

let rec pathToRegion = function (u, Here) -> toRegion u | (bind (r, None, u), Label (path)) -> r | (bind (r, Some (u1), u2), Label (path)) -> pathToRegion (u1, path) | (bind (r, _, u), Body (path)) -> pathToRegion (u, path) | (root (r, _, _, _, _), Label (path)) -> r | (u, Body (path)) -> pathToRegion (u, path) | (root (r, h, imp, actual, s), Head) -> toRegion h | (root (r, h, imp, actual, s), Arg (n, path)) -> if n <= imp then (* addressing implicit argument returns region of head *)
toRegion h else if n - imp > actual then (* addressing argument created by eta expansion
                approximate by the whole root *)
r else pathToRegionSpine (s, n - imp, path) | (leaf (r), _) -> r
and pathToRegionSpine = function (app (u, s), 1, path) -> pathToRegion (u, path) | (app (u, s), n, path) -> pathToRegionSpine (s, n - 1, path)
(* anything else should be impossible *)

(* occToRegionExp u occ = r,
     where r is the closest region including occ in occurrence tree u
  *)

let rec occToRegionExp u occ  = pathToRegion (u, occToPath (occ, Here))
let rec skipImplicit = function (0, path) -> path | (n, Body (path)) -> skipImplicit (n - 1, path) | (n, Label (path)) -> Here | (n, Here) -> Here
(* anything else should be impossible *)

(* occToRegionDec d occ = r
     where r is the closest region in v including occ for_sml declaration c : V
  *)

let rec occToRegionDec (dec (n, v)) occ  = pathToRegion (v, skipImplicit (n, occToPath (occ, Here)))
(* occToRegionDef1 d occ = r
     where r is the closest region in u including occ for_sml declaration c : V = U
  *)

let rec occToRegionDef1 (def (n, u, vOpt)) occ  = pathToRegion (u, skipImplicit (n, occToPath (occ, Here)))
(* occToRegionDef2 d occ = r
     where r is the closest region in V including occ for_sml declaration c : V = U
  *)

let rec occToRegionDef2 = function ((def (n, u, Some (v))), occ) -> pathToRegion (v, skipImplicit (n, occToPath (occ, Here))) | ((def (n, u, None)), occ) -> pathToRegion (u, Here)
(* occToRegionClause d occ = r
     where r is the closest region in V including occ for_sml declaration
     c : V or c : V = U.
  *)

let rec occToRegionClause = function ((d), occ) -> occToRegionDec d occ | ((d), occ) -> occToRegionDef2 d occ
 end


(* functor Paths *)


module Paths = Paths

