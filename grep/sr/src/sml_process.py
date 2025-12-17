"""Process SML to OCaml using tree-sitter SML grammar."""

from pathlib import Path
import sys
from typing import List, Optional

from tree_sitter import Language, Parser
import tree_sitter as TS

# Ensure the local Python binding is importable when the package isn't installed.
ROOT_DIR = Path(__file__).resolve().parents[1]
PY_BINDINGS = ROOT_DIR / "python"
if str(PY_BINDINGS) not in sys.path:
    sys.path.append(str(PY_BINDINGS))

import tree_sitter_sml

SML_LANGUAGE: Language = Language(tree_sitter_sml.language())
PARSER: Parser = Parser(SML_LANGUAGE)


def process_code(code: str) -> str:
    """Parse SML code and convert to OCaml."""
    tree: TS.Tree = PARSER.parse(code.encode("utf-8"))
    result = walk_tree(tree.root_node)
    return result


def get_text(node: TS.Node) -> str:
    """Get text from a node."""
    return node.text.decode("utf-8") if isinstance(node.text, bytes) else node.text


def process_name_lower(text: str) -> str:
    """Convert name to lowercase following OCaml conventions, unless it starts with uppercase (constructors)."""
    if not text:
        return text
    # If it starts with uppercase, keep it as-is (for constructors like NONE, SOME, List)
    if text[0].isupper():
        return text
    # Otherwise lowercase the first character for regular variables
    return text[0].lower() + text[1:] if len(text) > 1 else text.lower()


def process_name_upper(text: str) -> str:
    """Convert name to uppercase following OCaml conventions."""
    if not text:
        return text
    return text[0].upper() + text[1:] if len(text) > 1 else text.upper()


def walk_children(node: TS.Node) -> str:
    """Walk through all children and process them."""
    result = ""
    for child in node.children:
        if child.type not in ("block_comment", "line_comment"):
            result += walk_tree(child)
    return result


def walk_tree(node: TS.Node) -> str:
    """Main tree walking function to convert SML to OCaml."""
    
    match node.type:
        # Program structure
        case "source_file":
            # Separate top-level declarations with newlines
            result = ""
            for child in node.children:
                if child.type == ";":
                    result += "\n"
                else:
                    text = walk_tree(child)
                    if text:
                        result += text
            return result
        case "program":
            return walk_children(node)
        
        # Error handling
        case "ERROR":
            # When grammar can't parse, just return text as-is
            return get_text(node)
        
        # Comments
        case "comment" | "block_comment" | "line_comment":
            text = get_text(node)
            # Convert SML comments to OCaml: (* *) format is compatible
            return text + " "
        
        # Constants (special constants)
        case "integer_scon":
            return get_text(node)
        case "word_scon":
            # Convert SML word constants to OCaml
            text = get_text(node)
            # 0w123 in SML -> 0x123L in OCaml (approximate)
            if text.startswith("0w"):
                return "0x" + text[2:] + "L"
            return text
        case "real_scon":
            return get_text(node)
        case "string_scon":
            return get_text(node)
        case "char_scon":
            # SML: #"a" -> OCaml: 'a'
            text = get_text(node)
            if text.startswith("#"):
                return "'" + text[2:-1] + "'"
            return text
        
        # Identifiers
        case "vid":
            text = get_text(node)
            return process_name_lower(text)
        case "longvid":
            parts = []
            for child in node.children:
                if child.type == "vid":
                    parts.append(process_name_lower(get_text(child)))
                elif child.type not in (".", "strid"):
                    pass
            if not parts:
                parts.append(process_name_lower(get_text(node)))
            return ".".join(parts)
        case "tycon":
            # Type constructor - preserve case (int, bool, etc.)
            return get_text(node)
        case "longtycon":
            parts = []
            for child in node.children:
                if child.type == "tycon":
                    parts.append(get_text(child))
                elif child.type not in (".", "strid"):
                    pass
            if not parts:
                parts.append(get_text(node))
            return ".".join(parts)
        case "lab":
            text = get_text(node)
            return process_name_lower(text)
        case "tyvar":
            return get_text(node)
        case "strid":
            return get_text(node)
        case "sigid":
            return get_text(node)
        case "fctid":
            return get_text(node)
        
        # Expressions
        case "scon_exp":
            return walk_children(node)
        case "vid_exp":
            return walk_children(node)
        case "record_exp":
            # SML: {a=1, b=2} -> OCaml: {a = 1; b = 2}
            result = "{"
            first = True
            for child in node.children:
                if child.type == "exprow":
                    if not first:
                        result += "; "
                    result += walk_tree(child)
                    first = False
                elif child.type not in ("{", "}"):
                    pass
            result += "}"
            return result
        case "exprow":
            # exprow: lab = exp
            result = ""
            for child in node.children:
                if child.type == "lab":
                    result += walk_tree(child) + " = "
                elif child.type != "=":
                    result += walk_tree(child)
            return result
        case "labvar_exprow":
            # lab as id
            result = ""
            for child in node.children:
                if child.type == "lab":
                    result += walk_tree(child) + " = "
                elif child.type != "=":
                    result += walk_tree(child)
            return result
        case "ellipsis_exprow":
            return "..."
        case "recordsel_exp":
            # SML: #label exp -> OCaml: exp.label
            result = ""
            label = ""
            exp = ""
            for child in node.children:
                if child.type == "#":
                    pass
                elif child.type == "lab":
                    label = walk_tree(child)
                else:
                    exp = walk_tree(child)
            return exp + "." + label if exp else label
        case "unit_exp":
            return "()"
        case "tuple_exp":
            # SML: (a, b, c) -> OCaml: (a, b, c)
            result = "("
            first = True
            for child in node.children:
                if child.type not in ("(", ")", ","):
                    if not first:
                        result += ", "
                    result += walk_tree(child)
                    first = False
            result += ")"
            return result
        case "list_exp":
            # SML: [a, b, c] -> OCaml: [a; b; c]
            result = "["
            for child in node.children:
                if child.type == "[":
                    pass
                elif child.type == "]":
                    break
                elif child.type != ",":
                    result += walk_tree(child)
                else:
                    result += "; "
            result += "]"
            return result
        case "vec_exp":
            # SML: #[a, b] -> OCaml: [|a; b|]
            result = "[|"
            for child in node.children:
                if child.type not in ("#[", "]"):
                    if child.type != ",":
                        result += walk_tree(child)
                    else:
                        result += "; "
            result += "|]"
            return result
        case "sequence_exp":
            # SML: (a; b; c) -> OCaml: (a; b; c)
            result = "("
            for child in node.children:
                if child.type == "(":
                    pass
                elif child.type == ")":
                    break
                elif child.type != ";":
                    result += walk_tree(child)
                else:
                    result += "; "
            result += ")"
            return result
        case "let_exp":
            # SML: let val x = 1 in x + 1 end -> OCaml: let x = 1 in x + 1
            # Note: the val_dec already includes "let", so we don't add it again
            result = ""
            in_body = False
            declarations = []
            
            for child in node.children:
                if child.type == "let":
                    pass
                elif child.type == "in":
                    # Process all collected declarations
                    for decl in declarations:
                        result += walk_tree(decl) + " "
                    result += "in "
                    in_body = True
                elif child.type == "end":
                    break
                elif child.type.endswith("_dec"):
                    # Collect declarations to process when we hit 'in'
                    declarations.append(child)
                elif child.type == ";":
                    if in_body:
                        result += "; "
                elif child.type not in ("let",):
                    result += walk_tree(child)
                    
            return result
        case "paren_exp":
            result = "("
            for child in node.children:
                if child.type not in ("(", ")"):
                    result += walk_tree(child)
            result += ")"
            return result
        case "app_exp":
            result = ""
            first = True
            for child in node.children:
                if not first:
                    result += " "
                result += walk_tree(child)
                first = False
            return result
        case "typed_exp":
            # SML: (e : t) -> OCaml: (e : t)
            result = ""
            for i, child in enumerate(node.children):
                result += walk_tree(child)
                if i < len(node.children) - 1 and child.type != ":":
                    result += " : "
            return result
        case "conj_exp":
            # SML: e1 andalso e2 -> OCaml: e1 && e2
            return " && ".join(walk_tree(c) for c in node.children if c.type not in ("andalso",))
        case "disj_exp":
            # SML: e1 orelse e2 -> OCaml: e1 || e2
            return " || ".join(walk_tree(c) for c in node.children if c.type not in ("orelse",))
        case "handle_exp":
            # SML: e handle p => e' -> OCaml: try e with p -> e'
            result = "try "
            match_part = ""
            for child in node.children:
                if child.type == "handle":
                    result += " with "
                elif child.type == "_match":
                    match_part = walk_tree(child)
                    result += match_part
            return result
        case "raise_exp":
            result = "raise ("
            for child in node.children:
                if child.type != "raise":
                    result += walk_tree(child)
            result += ")"
            return result
        case "cond_exp":
            # SML: if c then e1 else e2 -> OCaml: if c then e1 else e2
            result = ""
            for child in node.children:
                if child.type == "if":
                    result += "if "
                elif child.type == "then":
                    result += " then "
                elif child.type == "else":
                    result += " else "
                elif child.type not in ("if", "then", "else"):
                    result += walk_tree(child)
            return result
        case "iter_exp":
            # SML: while c do e -> OCaml: while c do e done
            result = ""
            for child in node.children:
                if child.type == "while":
                    result += "while "
                elif child.type == "do":
                    result += " do "
                elif child.type not in ("while", "do"):
                    result += walk_tree(child)
            result += " done"
            return result
        case "case_exp":
            # SML: case e of p1 => e1 | p2 => e2 -> OCaml: match e with p1 -> e1 | p2 -> e2
            result = ""
            for child in node.children:
                if child.type == "case":
                    result += "match "
                elif child.type == "of":
                    result += " with "
                elif child.type == "mrule":
                    result += walk_tree(child)
                elif child.type == "|":
                    result += " | "
                elif child.type not in ("case", "of"):
                    result += walk_tree(child)
            return result
        case "fn_exp":
            # SML: fn p => e -> OCaml: fun p -> e
            result = "fun "
            for child in node.children:
                if child.type == "fn":
                    pass
                elif child.type == "mrule":
                    # Extract pattern and body
                    match_text = walk_tree(child)
                    result += match_text.replace(" => ", " -> ")
                elif child.type == "|":
                    result += " | "
                elif child.type != "fn":
                    result += walk_tree(child)
            return result
        case "_match" | "match":
            # Match rules
            result = ""
            for child in node.children:
                if child.type == "mrule":
                    result += walk_tree(child) + " | "
                elif child.type != "|" and child.type != "of":
                    result += walk_tree(child)
            return result.rstrip("| ")
        case "mrule":
            # SML: p => e -> OCaml: p -> e
            result = ""
            for child in node.children:
                if child.type == "=>":
                    result += " -> "
                else:
                    result += walk_tree(child)
            return result
        case "fmrule":
            # Function match rule: name pat1 pat2 ... = expr -> name pat1 pat2 ... = expr
            result = ""
            found_equals = False
            for child in node.children:
                if child.type == "=":
                    result += " = "
                    found_equals = True
                elif child.type != "=":
                    result += walk_tree(child) + " "
            return result.rstrip()
        case "_fmatch":
            return walk_children(node)
        
        # Declarations
        case "val_dec":
            # SML: val x = e -> OCaml: let x = e
            result = "let "
            is_rec = False
            valbinds = []
            
            for child in node.children:
                if child.type == "rec":
                    is_rec = True
                elif child.type == "valbind":
                    valbinds.append(child)
            
            if is_rec:
                result = "let rec "
            
            # Process all valbinds, joining with ' and '
            for i, valbind in enumerate(valbinds):
                if i > 0:
                    result += " and "
                result += walk_tree(valbind)
            
            return result
        case "valbind":
            # SML: pat = exp
            result = ""
            for child in node.children:
                if child.type == "=":
                    result += " = "
                elif child.type not in ("and",):
                    result += walk_tree(child)
            return result
        case "fun_dec":
            # SML: fun f x = e -> OCaml: let rec f x = e
            result = "let rec "
            for child in node.children:
                if child.type == "fun":
                    pass
                elif child.type == "fvalbind":
                    result += walk_tree(child)
                else:
                    result += walk_tree(child)
            return result
        case "_fvalbind":
            # Process all fvalbind nodes, joining with 'and'
            result = ""
            first = True
            for child in node.children:
                if child.type == "fvalbind":
                    if not first:
                        result += " and "
                    result += walk_tree(child)
                    first = False
                elif child.type == "and":
                    pass
            return result
        case "fvalbind":
            # Contains fmrule(s)
            result = ""
            for child in node.children:
                if child.type == "fmrule":
                    result += walk_tree(child)
                elif child.type == "|":
                    result += " | "
            return result
        case "type_dec":
            # SML: type t = ... -> OCaml: type t = ...
            result = "type "
            typbinds = []
            
            for child in node.children:
                if child.type == "typbind":
                    typbinds.append(child)
            
            # Process all typbinds, joining with ' and '
            for i, typbind in enumerate(typbinds):
                if i > 0:
                    result += " and "
                result += walk_tree(typbind)
            
            return result
        case "_typbind":
            # Shouldn't appear, but handle if it does
            result = ""
            typbinds = []
            for child in node.children:
                if child.type == "typbind":
                    typbinds.append(child)
            
            for i, typbind in enumerate(typbinds):
                if i > 0:
                    result += " and "
                result += walk_tree(typbind)
            return result
        case "typbind":
            # type name = type
            result = ""
            for child in node.children:
                if child.type == "tycon":
                    result += walk_tree(child)
                elif child.type == "=":
                    result += " = "
                elif child.type not in ("and",):
                    result += walk_tree(child)
            return result
        case "datatype_dec":
            # SML: datatype t = C1 | C2 -> OCaml: type t = C1 | C2
            result = "type "
            datbinds = []
            
            for child in node.children:
                if child.type == "datbind":
                    datbinds.append(child)
            
            # Process all datbinds, joining with ' and '
            for i, datbind in enumerate(datbinds):
                if i > 0:
                    result += " and "
                result += walk_tree(datbind)
            
            return result
        case "_datbind":
            # Handle multiple datbind with 'and'
            result = ""
            first = True
            for child in node.children:
                if child.type == "datbind":
                    if not first:
                        result += " and "
                    result += walk_tree(child)
                    first = False
                elif child.type == "and":
                    pass
            return result
        case "datbind":
            # SML: tycon = conbind | conbind | ...
            result = ""
            conbinds = []
            
            for child in node.children:
                if child.type == "tycon":
                    result += walk_tree(child)
                elif child.type == "=":
                    result += " = "
                elif child.type == "conbind":
                    conbinds.append(child)
            
            # Process all conbinds, joining with ' | '
            for i, conbind in enumerate(conbinds):
                if i > 0:
                    result += " | "
                result += walk_tree(conbind)
            
            return result
        case "_conbind":
            # Handle multiple conbind with '|'
            result = ""
            conbinds = []
            for child in node.children:
                if child.type == "conbind":
                    conbinds.append(child)
            
            for i, conbind in enumerate(conbinds):
                if i > 0:
                    result += " | "
                result += walk_tree(conbind)
            return result
        case "conbind":
            result = ""
            for child in node.children:
                if child.type == "vid":
                    result += walk_tree(child)
                elif child.type == "of":
                    result += " of "
                elif child.type not in ("vid", "of"):
                    result += walk_tree(child)
            return result
        case "exception_dec":
            # exception name or exception name of type
            result = "exception "
            exbinds = []
            
            for child in node.children:
                if child.type == "exbind":
                    exbinds.append(child)
            
            # Process all exbinds, joining with ' and '
            for i, exbind in enumerate(exbinds):
                if i > 0:
                    result += " and "
                result += walk_tree(exbind)
            
            return result
        case "_exbind":
            # Handle multiple exbind with 'and'
            result = ""
            exbinds = []
            for child in node.children:
                if child.type == "exbind":
                    exbinds.append(child)
            
            for i, exbind in enumerate(exbinds):
                if i > 0:
                    result += " and "
                result += walk_tree(exbind)
            return result
        case "exbind":
            # exception name or exception name of type
            result = ""
            for child in node.children:
                if child.type == "vid":
                    result += walk_tree(child)
                elif child.type == "of":
                    result += " of "
                elif child.type not in ("vid", "of", "="):
                    result += walk_tree(child)
            return result
        case "local_dec":
            # SML: local decs in decs end -> OCaml: local decs in decs end (same syntax)
            result = "local "
            in_found = False
            for child in node.children:
                if child.type == "local":
                    pass
                elif child.type == "in":
                    result += " in "
                    in_found = True
                elif child.type == "end":
                    result += " end"
                    break
                elif child.type not in ("local", ";"):
                    result += walk_tree(child)
                    if not in_found:
                        result += "; "
            return result
        case "open_dec":
            # SML: open Module -> OCaml: open Module
            result = "open "
            for child in node.children:
                if child.type == "open":
                    pass
                elif child.type == "longstrid":
                    result += walk_tree(child)
            return result
        case "infix_dec":
            # SML: infix id -> OCaml: not directly supported, skip
            return ""
        case "infixr_dec":
            return ""
        case "nonfix_dec":
            return ""
        
        # Patterns
        case "wildcard_pat":
            return "_"
        case "scon_pat":
            return walk_children(node)
        case "vid_pat":
            return walk_children(node)
        case "record_pat":
            result = "{"
            first = True
            for child in node.children:
                if child.type not in ("{", "}", ","):
                    if not first:
                        result += "; "
                    result += walk_tree(child)
                    first = False
            result += "}"
            return result
        case "_patrow":
            return walk_children(node)
        case "patrow":
            result = ""
            for child in node.children:
                if child.type == "lab":
                    result += walk_tree(child) + " = "
                elif child.type != "=":
                    result += walk_tree(child)
            return result
        case "labvar_patrow":
            return walk_children(node)
        case "ellipsis_patrow":
            return "_"
        case "unit_pat":
            return "()"
        case "tuple_pat":
            result = "("
            first = True
            for child in node.children:
                if child.type not in ("(", ")", ","):
                    if not first:
                        result += ", "
                    result += walk_tree(child)
                    first = False
            result += ")"
            return result
        case "list_pat":
            result = "["
            first = True
            for child in node.children:
                if child.type not in ("[", "]"):
                    if not first and child.type != ",":
                        result += "; "
                    if child.type != ",":
                        result += walk_tree(child)
                    first = False
            result += "]"
            return result
        case "vec_pat":
            result = "[|"
            first = True
            for child in node.children:
                if child.type not in ("#[", "]"):
                    if not first and child.type != ",":
                        result += "; "
                    if child.type != ",":
                        result += walk_tree(child)
                    first = False
            result += "|]"
            return result
        case "paren_pat":
            result = "("
            for child in node.children:
                if child.type not in ("(", ")"):
                    result += walk_tree(child)
            result += ")"
            return result
        case "app_pat":
            result = ""
            first = True
            for child in node.children:
                if not first:
                    result += " "
                result += walk_tree(child)
                first = False
            return result
        case "typed_pat":
            result = ""
            for child in node.children:
                if child.type == ":":
                    result += " : "
                else:
                    result += walk_tree(child)
            return result
        case "as_pat":
            # SML: pat as id -> OCaml: pat as id
            result = ""
            for child in node.children:
                if child.type == "as":
                    result += " as "
                else:
                    result += walk_tree(child)
            return result
        case "conj_pat":
            result = ""
            for child in node.children:
                if child.type == "as":
                    result += " as "
                else:
                    result += walk_tree(child)
            return result
        case "disj_pat":
            # SML: p1 | p2 -> OCaml: not directly supported in patterns
            result = ""
            for child in node.children:
                if child.type == "|":
                    result += " | "
                else:
                    result += walk_tree(child)
            return result
        
        # Types
        case "fn_ty":
            # SML: t1 -> t2 -> OCaml: t1 -> t2
            result = ""
            for child in node.children:
                if child.type == "->":
                    result += " -> "
                else:
                    result += walk_tree(child)
            return result
        case "tuple_ty":
            # SML: t1 * t2 -> OCaml: t1 * t2
            result = ""
            first = True
            for child in node.children:
                if child.type == "*":
                    result += " * "
                else:
                    if not first:
                        pass
                    result += walk_tree(child)
                    first = False
            return result
        case "paren_ty":
            result = "("
            for child in node.children:
                if child.type not in ("(", ")"):
                    result += walk_tree(child)
            result += ")"
            return result
        case "tyvar_ty":
            return walk_children(node)
        case "record_ty":
            result = "{"
            first = True
            for child in node.children:
                if child.type not in ("{", "}", ","):
                    if not first:
                        result += "; "
                    result += walk_tree(child)
                    first = False
            result += "}"
            return result
        case "tyrow":
            result = ""
            for child in node.children:
                if child.type == "lab":
                    result += walk_tree(child) + ": "
                elif child.type != ":":
                    result += walk_tree(child)
            return result
        case "tycon_ty":
            # type constructor possibly with type parameters: 'a array, int, etc.
            result = ""
            for child in node.children:
                if child.type not in ("(", ")"):
                    result += walk_tree(child)
                    if child.type in ("tyseq", "tyvar"):
                        result += " "  # Space after type parameters
            return result.rstrip()
        
        # Structure/Module expressions
        case "struct_strexp":
            result = "struct "
            for child in node.children:
                if child.type == "struct":
                    pass
                elif child.type == "end":
                    result += "end"
                    break
                elif child.type != ";":
                    result += walk_tree(child) + " "
            return result
        case "strid_strexp":
            return walk_children(node)
        case "constr_strexp":
            # SML: strexp : sigexp -> OCaml: (strexp : module sig)
            result = "("
            for child in node.children:
                if child.type == ":":
                    result += " : "
                elif child.type == ":>":
                    result += " : "
                else:
                    result += walk_tree(child)
            result += ")"
            return result
        case "fctapp_strexp":
            # SML: Fct (arg1 arg2 ...) -> OCaml: Fct(struct arg1 arg2 ... end)
            # When there are multiple structure declarations, wrap in struct...end
            result = ""
            args = []
            for child in node.children:
                if child.type == "fctid":
                    result += walk_tree(child)
                elif child.type == "(":
                    result += "("
                elif child.type == ")":
                    # If multiple args, wrap in struct...end
                    if len(args) > 1:
                        result += "struct " + " ".join(args) + " end"
                    elif args:
                        result += args[0]
                    result += ")"
                elif child.type in ("structure_strdec", "sigexp"):
                    args.append(walk_tree(child))
            return result
        case "let_strexp":
            # SML: let decs in strexp end -> OCaml: let decs in strexp
            result = "let "
            in_found = False
            for child in node.children:
                if child.type == "let":
                    pass
                elif child.type == "in":
                    result += " in "
                    in_found = True
                elif child.type == "end":
                    break
                elif child.type.endswith("_dec"):
                    result += walk_tree(child) + " "
                elif child.type not in (";", "let"):
                    result += walk_tree(child)
            return result
        case "_strdec":
            # This shouldn't appear as a node since it's anonymous, but handle if it does
            return walk_children(node)
        case "structure_strdec":
            result = "module "
            for child in node.children:
                if child.type == "structure":
                    pass
                elif child.type == "strbind":
                    result += walk_tree(child)
                elif child.type == "and":
                    result += " and "
            return result
        case "_strbind":
            # Handle multiple strbind with 'and'
            result = ""
            first = True
            for child in node.children:
                if child.type == "strbind":
                    if not first:
                        result += " and "
                    result += walk_tree(child)
                    first = False
                elif child.type == "and":
                    pass
            return result
        case "strbind":
            result = ""
            for child in node.children:
                if child.type == "strid":
                    result += walk_tree(child)
                elif child.type == "=":
                    result += " = "
                elif not child.type.endswith("_"):
                    result += walk_tree(child)
            return result
        case "local_strdec":
            result = ""
            in_found = False
            for child in node.children:
                if child.type == "local":
                    pass
                elif child.type == "in":
                    in_found = True
                elif child.type == "end":
                    break
                elif child.type.endswith("_dec"):
                    result += walk_tree(child) + " "
                elif child.type != ";":
                    result += walk_tree(child)
            return result
        
        # Signature expressions
        case "sig_sigexp":
            result = "sig "
            for child in node.children:
                if child.type == "sig":
                    pass
                elif child.type == "end":
                    result += " end"
                    break
                elif child.type == ";":
                    result += "\n"
                else:
                    text = walk_tree(child)
                    if text:
                        result += text
            return result
        case "sigid_sigexp":
            return walk_children(node)
        case "wheretype_sigexp":
            # SML: sigexp where type ... = ...
            result = ""
            for child in node.children:
                if child.type == "where":
                    result += " where "
                elif child.type not in ("where",):
                    result += walk_tree(child)
            return result
        
        # Signature specifications
        case "val_spec":
            # SML: val name : type -> OCaml: val name : type
            result = "val "
            for child in node.children:
                if child.type == "val":
                    pass
                elif child.type == "valdesc":
                    result += walk_tree(child)
                elif child.type == "and":
                    result += " and "
            return result
        case "type_spec":
            result = "type "
            for child in node.children:
                if child.type == "type":
                    pass
                elif child.type == "typedesc" or child.type == "typbind":
                    result += walk_tree(child)
                elif child.type == "and":
                    result += " and "
            return result
        case "eqtype_spec":
            result = "type "
            for child in node.children:
                if child.type == "eqtype":
                    pass
                elif child.type == "typedesc":
                    result += walk_tree(child)
            return result
        case "datatype_spec":
            result = "type "
            for child in node.children:
                if child.type == "datatype":
                    pass
                elif child.type == "datdesc":
                    result += walk_tree(child)
                elif child.type == "and":
                    result += " and "
            return result
        case "exception_spec":
            result = "exception "
            for child in node.children:
                if child.type == "exception":
                    pass
                elif child.type == "exdesc":
                    result += walk_tree(child)
                elif child.type == "and":
                    result += " and "
            return result
        case "structure_spec":
            result = "module "
            for child in node.children:
                if child.type == "structure":
                    pass
                elif child.type == "strdesc":
                    result += walk_tree(child)
                elif child.type == "and":
                    result += " and "
            return result
        case "include_spec":
            result = "include "
            for child in node.children:
                if child.type == "include":
                    pass
                elif child.type not in ("include",):
                    result += walk_tree(child)
            return result
        
        # Descriptors (used in specs)
        case "valdesc":
            # name : type
            result = ""
            for child in node.children:
                if child.type == "vid":
                    result += walk_tree(child)
                elif child.type == ":":
                    result += " : "
                elif child.type not in (":", "and"):
                    result += walk_tree(child)
            return result
        case "typedesc":
            # type name or type 'a name
            result = ""
            for child in node.children:
                if child.type == "tycon":
                    result += walk_tree(child)
                elif child.type not in ("=", "and"):
                    result += walk_tree(child)
            return result
        case "strdesc":
            # structure name : sig
            result = ""
            for child in node.children:
                if child.type == "strid":
                    result += walk_tree(child)
                elif child.type == ":":
                    result += " : "
                elif child.type not in (":", "and"):
                    result += walk_tree(child)
            return result
        case "exdesc":
            # exception name or exception name of type
            result = ""
            for child in node.children:
                if child.type == "vid":
                    result += walk_tree(child)
                elif child.type == "of":
                    result += " of "
                elif child.type not in ("of", "and"):
                    result += walk_tree(child)
            return result
        
        # Functor declarations and bindings
        case "functor_fctdec":
            result = "module "
            for child in node.children:
                if child.type == "functor":
                    pass 
                elif child.type == "fctbind":
                    result += walk_tree(child)
                elif child.type == "and":
                    result += " and "
            return result
        case "fctbind":
            # Functor binding: name (arg : sig) : sig = strexp
            result = ""
            for child in node.children:
                if child.type == "fctid":
                    result += walk_tree(child)
                elif child.type in (":", "="):
                    result += " " + child.type + " "
                elif child.type == "(":
                    result += " ("
                elif child.type == ")":
                    result += ")"
                elif child.type != "fctid":
                    text = walk_tree(child)
                    if text:
                        result += text
            return result
        
        # Signature declarations
        case "signature_sigdec":
            result = "module type "
            for child in node.children:
                if child.type == "signature":
                    pass
                elif child.type == "sigbind":
                    result += walk_tree(child)
                elif child.type == "and":
                    result += " and "
            return result
        case "sigbind":
            # signature name = sigexp
            result = ""
            for child in node.children:
                if child.type == "sigid":
                    result += walk_tree(child)
                elif child.type == "=":
                    result += " = "
                elif child.type not in ("sigid", "="):
                    result += walk_tree(child)
            return result
        
        # Default case: walk children (for unhandled node types)
        case _:
            return walk_children(node)


# Example usage
if __name__ == "__main__":
    sml_code = """
    val x = 5
    fun fib n = if n <= 1 then n else fib (n-1) + fib (n-2)
    val result = fib 10
    """
    
    ocaml_code = process_code(sml_code)
    print("Converted OCaml code:")
    print(ocaml_code)