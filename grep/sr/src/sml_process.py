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
    """Convert name to lowercase following OCaml conventions."""
    if not text:
        return text
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
            return walk_children(node)
        case "program":
            return walk_children(node)
        
        # Comments
        case "comment" | "block_comment" | "line_comment":
            text = get_text(node)
            # Convert SML comments to OCaml: (* *) format is compatible
            return text + "\n"
        
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
            text = get_text(node)
            return process_name_upper(text)
        case "longtycon":
            parts = []
            for child in node.children:
                if child.type == "tycon":
                    parts.append(process_name_upper(get_text(child)))
                elif child.type not in (".", "strid"):
                    pass
            if not parts:
                parts.append(process_name_upper(get_text(node)))
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
            for child in node.children:
                if child.type == "exprow":
                    for subchild in child.children:
                        result += walk_tree(subchild)
                        if subchild.type == "lab":
                            result += " = "
                        elif subchild.type not in ("=",):
                            result += walk_tree(subchild) if subchild.type != "lab" else ""
                elif child.type not in ("{", "}", ","):
                    result += walk_tree(child)
                elif child.type == ",":
                    result += "; "
            result += "}"
            return result
        case "exprow":
            result = ""
            for child in node.children:
                if child.type == "lab":
                    result += walk_tree(child) + " = "
                elif child.type != "=":
                    result += walk_tree(child)
            return result
        case "labvar_exprow":
            return walk_children(node)
        case "ellipsis_exprow":
            return walk_children(node)
        case "recordsel_exp":
            # SML: #label exp -> OCaml: exp.label
            return walk_children(node)
        case "unit_exp":
            return "()"
        case "tuple_exp":
            # SML: (a, b, c) -> OCaml: (a, b, c)
            result = "("
            first = True
            for child in node.children:
                if child.type not in ("(", ")"):
                    if (not first) and child.type != ",":
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
            result = "let "
            in_body = False
            for child in node.children:
                if child.type == "let":
                    pass
                elif child.type == "in":
                    result += " in "
                    in_body = True
                elif child.type == "end":
                    break
                elif child.type == "_dec":
                    result += walk_tree(child)
                    if not in_body:
                        result += " "
                elif child.type != ";":
                    result += walk_tree(child)
            result += ""
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
                elif child.type == "_match":
                    result += walk_tree(child)
                elif child.type != "case" and child.type != "of":
                    result += walk_tree(child)
            return result
        case "fn_exp":
            # SML: fn p => e -> OCaml: fun p -> e
            result = "fun "
            for child in node.children:
                if child.type == "fn":
                    pass
                elif child.type == "_match":
                    # Extract pattern and body
                    match_text = walk_tree(child)
                    result += match_text.replace(" => ", " -> ")
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
            # Function match rule
            return walk_children(node)
        case "_fmatch":
            return walk_children(node)
        
        # Declarations
        case "val_dec":
            # SML: val x = e -> OCaml: let x = e
            result = "let "
            for child in node.children:
                if child.type == "val":
                    pass
                elif child.type == "valbind":
                    result += walk_tree(child)
                elif child.type == "rec":
                    result = "let rec "
                else:
                    result += walk_tree(child)
            result += " in"
            return result
        case "valbind":
            result = ""
            for child in node.children:
                if child.type == "_pat":
                    result += walk_tree(child)
                elif child.type == "_exp":
                    result += " = " + walk_tree(child)
                elif child.type == "=":
                    pass
            return result
        case "fun_dec":
            # SML: fun f x = e -> OCaml: let rec f x = e
            result = "let rec "
            for child in node.children:
                if child.type == "fun":
                    pass
                elif child.type == "_fvalbind":
                    result += walk_tree(child)
                else:
                    result += walk_tree(child)
            return result
        case "_fvalbind":
            return walk_children(node)
        case "fvalbind":
            return walk_children(node)
        case "type_dec":
            # SML: type t = ... -> OCaml: type t = ...
            result = "type "
            for child in node.children:
                if child.type == "type":
                    pass
                elif child.type == "_typbind":
                    result += walk_tree(child)
                else:
                    result += walk_tree(child)
            return result
        case "_typbind":
            result = ""
            for child in node.children:
                if child.type == "typbind":
                    result += walk_tree(child)
                elif child.type == "and":
                    result += " and "
            return result
        case "typbind":
            result = ""
            for child in node.children:
                if child.type == "tycon":
                    result += walk_tree(child)
                elif child.type == "_ty":
                    result += " = " + walk_tree(child)
                elif child.type == "=":
                    pass
            return result
        case "datatype_dec":
            # SML: datatype t = C1 | C2 -> OCaml: type t = C1 | C2
            result = "type "
            for child in node.children:
                if child.type == "datatype":
                    pass
                elif child.type == "_datbind":
                    result += walk_tree(child)
                else:
                    result += walk_tree(child)
            return result
        case "_datbind":
            return walk_children(node)
        case "datbind":
            result = ""
            for child in node.children:
                if child.type == "tycon":
                    result += walk_tree(child)
                elif child.type == "_conbind":
                    result += " = " + walk_tree(child)
                elif child.type == "=":
                    pass
            return result
        case "_conbind":
            result = ""
            first = True
            for child in node.children:
                if child.type == "conbind":
                    if not first:
                        result += " | "
                    result += walk_tree(child)
                    first = False
                elif child.type == "|":
                    pass
            return result
        case "conbind":
            result = ""
            for child in node.children:
                if child.type == "vid":
                    result += walk_tree(child)
                elif child.type == "of":
                    result += " of "
                elif child.type == "_ty":
                    result += walk_tree(child)
            return result
        case "exception_dec":
            result = "exception "
            for child in node.children:
                if child.type == "exception":
                    pass
                elif child.type == "_exbind":
                    result += walk_tree(child)
            return result
        case "_exbind":
            return walk_children(node)
        case "exbind":
            return walk_children(node)
        case "local_dec":
            # SML: local decs in decs end -> OCaml: decs in decs
            result = ""
            in_found = False
            for child in node.children:
                if child.type == "local":
                    pass
                elif child.type == "in":
                    in_found = True
                elif child.type == "end":
                    break
                elif child.type == "_dec":
                    if in_found:
                        result += walk_tree(child) + " "
                    else:
                        result += walk_tree(child) + " "
                elif child.type not in (";",):
                    result += walk_tree(child)
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
                if child.type not in ("(", ")"):
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
            result = ""
            for child in node.children:
                if child.type not in ("(", ")"):
                    result += walk_tree(child)
            return result
        
        # Structure/Module expressions
        case "struct_strexp":
            result = "struct "
            for child in node.children:
                if child.type == "struct":
                    pass
                elif child.type == "end":
                    result += "end"
                elif child.type == "_strdec":
                    result += walk_tree(child) + " "
                elif child.type != ";":
                    result += walk_tree(child)
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
                    result += " :> "
                else:
                    result += walk_tree(child)
            result += ")"
            return result
        case "_strdec":
            return walk_children(node)
        case "structure_strdec":
            result = "module "
            for child in node.children:
                if child.type == "structure":
                    pass
                elif child.type == "_strbind":
                    result += walk_tree(child)
            return result
        case "_strbind":
            return walk_children(node)
        case "strbind":
            result = ""
            for child in node.children:
                if child.type == "strid":
                    result += walk_tree(child)
                elif child.type == ":":
                    result += " : "
                elif child.type == ":>":
                    result += " :> "
                elif child.type == "=":
                    result += " = "
                elif child.type == "_strexp":
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
                elif child.type == "_strdec":
                    result += walk_tree(child) + " "
                elif child.type != ";":
                    result += walk_tree(child)
            return result
        
        # Default case: walk children
        case _:
            return walk_children(node) + " "


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