"""Process SML to OCaml using tree-sitter SML grammar."""

from pathlib import Path
import sys
import re
from typing import List, Optional

from tree_sitter import Language, Parser
import tree_sitter as TS
import tree_sitter_ocaml

# Ensure the local Python binding is importable when the package isn't installed.
ROOT_DIR = Path(__file__).resolve().parents[1]
PY_BINDINGS = ROOT_DIR / "python"
if str(PY_BINDINGS) not in sys.path:
    sys.path.append(str(PY_BINDINGS))

import tree_sitter_sml

SML_LANGUAGE: Language = Language(tree_sitter_sml.language())
PARSER: Parser = Parser(SML_LANGUAGE)

OCAML_LANGUAGE: Language = Language(tree_sitter_ocaml.language_ocaml())
OCAML_PARSER: Parser = Parser(OCAML_LANGUAGE)

# Minimal renames for identifiers that collide with OCaml keywords.
OCAML_RESERVED_RENAMES = {
    "new": "new_",
    "match": "match_",
    "try": "try_",
    "type": "type_",
    "module": "module_",
    "struct": "struct_",
    "sig": "sig_",
    "object": "object_",
    "class": "class_",
    "constraint": "constraint_",
    "method": "method_",
    "fun": "fun_",
    "function": "function_",
    "to": "to_",
    "do": "do_",
    "done": "done_",
    "begin": "begin_",
    "end": "end_",
    "if": "if_",
    "then": "then_",
    "else": "else_",
    "in": "in_",
    "let": "let_",
    "rec": "rec_",
    "and": "and_",
    "or": "or_",
    "land": "land_",
    "lor": "lor_",
    "lsl": "lsl_",
    "lsr": "lsr_",
    "lxor": "lxor_",
    "mod": "mod_",
    "when": "when_",
    "while": "while_",
    "for": "for_",
    "downto": "downto_",
    "val": "val_",
    "open": "open_",
    "include": "include_",
    "inherit": "inherit_",
    "initializer": "initializer_",
}

OPERATOR_CHARS = set("!$%&*+-/:<=>?@^|~")


def _is_operator(text: str) -> bool:
    return bool(text) and all(ch in OPERATOR_CHARS for ch in text)


def _format_operator(text: str, prefix: str | None = None) -> str:
    formatted = f"( {text} )"
    return f"{prefix}.{formatted}" if prefix else formatted


def _convert_char_literal(text: str) -> str:
    """Convert SML char literal (e.g., #"a", #"\\^D") to an OCaml-compatible char."""
    if not (text.startswith("#\"") and text.endswith("\"")):
        return text

    body = text[2:-1]

    # Control character notation \^X
    if body.startswith("\\^") and len(body) >= 3:
        ctrl = body[2]
        code = ord(ctrl.upper()) - 64  # Ctrl+A == 1
        code = max(0, min(code, 0o377))
        return f"'\\{code:03o}'"

    # Common escape sequences
    escapes = {
        "n": "\\n",
        "t": "\\t",
        "r": "\\r",
        "b": "\\b",
        "f": "\\f",
        "\\": "\\\\",
        "\"": "\"",
        "'": "\\'",
    }

    if body.startswith("\\"):
        esc = body[1:]
        if esc and esc[0].isdigit():
            try:
                val_int = int(esc, 10)
                val_int = max(0, min(val_int, 0o377))
                return f"'\\{val_int:03o}'"
            except ValueError:
                pass
        mapped = escapes.get(esc, "\\" + esc)
        return f"'{mapped}'"

    # Plain character
    body = body.replace("'", "\\'")
    return f"'{body}'"

# SML to OCaml name mappings for standard library
SML_TO_OCAML_NAMES = {
    "SOME": "Some",
    "NONE": "None",
    "nil": "[]",
    "true": "true",
    "false": "false",
    "LESS": "Lt",
    "EQUAL": "Eq",
    "GREATER": "Gt",
}

type context = int 
SIMP_CONTEXT : context = 0
TYPE_CONTEXT : context = 1 
TERM_CONTEXT : context = 2
DECL_CONTEXT : context = 3

def process_code(code: str) -> str:
    """Parse SML code and convert to OCaml."""
    tree: TS.Tree = PARSER.parse(code.encode("utf-8"))
    result = walk_tree(tree.root_node)
    # Drop alias patterns (`x as pat`) that frequently appear in SML but
    # trip the OCaml parser in the converted output. Keeping only the
    # right-hand pattern preserves structure while improving parse rates.
    result = re.sub(r"\b\w+\s+as\s+", "", result)
    # Local type declarations inside function bodies are not valid in OCaml;
    # comment them out to keep the parser happy while preserving the surrounding code.
    result = re.sub(r"type \([^)]*\) change = CHANGE of \{[^}]*\}", "", result)

    return result

def get_text(node: TS.Node) -> str:
    """Get text from a node."""
    return node.text.decode("utf-8") if isinstance(node.text, bytes) else node.text


def sanitize_typevar(text: str) -> str:
    """Normalize SML type variables to OCaml-friendly form (drop leading underscores)."""
    if not text:
        return text
    if text.startswith("'_"):
        # OCaml type vars cannot start with `_`, so map to a regular name.
        return "'a" + text[2:]
    return text


def process_name_lower(text: str) -> str:
    """Convert name to lowercase following OCaml conventions, unless it starts with uppercase (constructors)."""
    if not text:
        return text
    text = OCAML_RESERVED_RENAMES.get(text, text)
    # If it starts with uppercase, keep it as-is (for constructors like NONE, SOME, List)
    if text[0].isupper():
        return text
    # Otherwise lowercase the first character for regular variables
    return text[0].lower() + text[1:] if len(text) > 1 else text.lower()


def process_name_upper(text: str) -> str:
    """Convert name to uppercase following OCaml conventions."""
    if not text:
        return text
    text = OCAML_RESERVED_RENAMES.get(text, text)
    return text[0].upper() + text[1:] if len(text) > 1 else text.upper()


def walk_children(node: TS.Node, context: context = SIMP_CONTEXT) -> str:
    """Walk through all children and process them."""
    result = ""
    for child in node.children:
        if child.type not in ("block_comment", "line_comment"):
            result += walk_tree(child, context)
    return result
def process_number(node : TS.Node) -> str:
    if get_text(node).strip()[0] == "~":
        return get_text(node).replace("~", "-")
    else: 
        return get_text(node)
def node_is_type(node : TS.Node) -> bool:
    return node.type.endswith("_ty")
def walk_tree(node: TS.Node, context: context = SIMP_CONTEXT) -> str:
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
                        if result and not result.endswith(";;\n"):
                            result += "\n"
                        result += text
                        if not result.endswith(";;\n"):
                            result += "\n"
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
            return text + "\n"
        
        # Constants (special constants)
        case "integer_scon":
            return process_number(node)
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
            return _convert_char_literal(text)
        
        # Identifiers
        case "vid":
            text = get_text(node)
            # Don't wrap operators here - just return them as-is.
            # Context (infix vs. prefix) is handled by parent nodes.
            if text in SML_TO_OCAML_NAMES:
                return SML_TO_OCAML_NAMES[text]
            if _is_operator(text):
                return text
            return process_name_lower(text)
        case "longvid":
            parts = []
            for child in node.children:
                if child.type == "strid":
                    parts.append(get_text(child))
                elif child.type == "vid":
                    text = get_text(child)
                    if text in SML_TO_OCAML_NAMES:
                        parts.append(SML_TO_OCAML_NAMES[text])
                    elif _is_operator(text):
                        parts.append(text)
                    else:
                        parts.append(process_name_lower(text))
                elif child.type != ".":
                    pass
            if not parts:
                text = get_text(node)
                if text in SML_TO_OCAML_NAMES:
                    parts.append(SML_TO_OCAML_NAMES[text])
                elif _is_operator(text):
                    parts.append(text)
                else:
                    parts.append(process_name_lower(text))

            return ".".join(parts)
        case "tycon":
            # Type constructor - OCaml type names must be lowercase
            text = get_text(node)
            return text[0].lower() + text[1:] if text else text
        case "longtycon":
            parts = []
            for child in node.children:
                if child.type == "strid":
                    parts.append(get_text(child))
                elif child.type == "tycon":
                    text = get_text(child)
                    parts.append(text[0].lower() + text[1:] if text else text)
                elif child.type != ".":
                    pass
            if not parts:
                text = get_text(node)
                parts.append(text[0].lower() + text[1:] if text else text)
            return ".".join(parts)
        case "lab":
            text = get_text(node)
            return process_name_lower(text)
        case "tyvar":
            return sanitize_typevar(get_text(node))
        case "tyvarseq":
            # Type variable sequence: 'a or ('a, 'b) - add space after for types
            result = ""
            for child in node.children:
                if child.type not in ("(", ")", ","):
                    if result:
                        result += ", "
                    result += walk_tree(child)
            # Wrap in parens if multiple type vars
            if ", " in result:
                result = "(" + result + ")"
            return result
        case "tyseq":
            # Type sequence in type application
            result = ""
            for child in node.children:
                if child.type not in ("(", ")", ","):
                    if result:
                        result += ", "
                    result += walk_tree(child)
            # Wrap in parens if multiple type args
            if ", " in result:
                result = "(" + result + ")"
            return result
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
            # Map record expressions directly to OCaml records
            fields = []
            for child in node.children:
                if child.type in ("{", "}", ","):
                    continue
                fields.append(walk_tree(child))
            return "{" + "; ".join(fields) + "}"
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
                if child.type in ("(", ")", ","):
                    continue
                if child.type in ("comment", "block_comment", "line_comment"):
                    # Preserve comment placement without affecting separators
                    result += walk_tree(child)
                    continue
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
            past_type = False
            declarations = []
            
            for child in node.children:
                if child.type == "let":
                    pass

                elif child.type == "in":
                    # Process all collected declarations
                    for decl in declarations:
                        result += walk_tree(decl) + " in "
                    result += " "
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
                    
            return ("( " + result + " )")
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
            # SML: e : t -> OCaml: (e : t)
            # Wrap in parens so trailing type constraints stay inside expressions
            result = ""
            for i, child in enumerate(node.children):
                result += walk_tree(child)
                if i < len(node.children) - 1 and child.type != ":":
                    result += " : "
            return f"({result})"
        case "conj_exp":
            # SML: e1 andalso e2 -> OCaml: e1 && e2
            return " && ".join(walk_tree(c) for c in node.children if c.type not in ("andalso",))
        case "disj_exp":
            # SML: e1 orelse e2 -> OCaml: e1 || e2
            return " || ".join(walk_tree(c) for c in node.children if c.type not in ("orelse",))
        case "handle_exp":
            # SML: e handle p => e' -> OCaml: try e with p -> e'
            handled = ""
            handler_rules: List[str] = []
            saw_handle = False
            for child in node.children:
                if child.type == "handle":
                    saw_handle = True
                elif child.type == "_match":
                    match_text = walk_tree(child)
                    if match_text:
                        handler_rules.append(match_text)
                elif child.type in ("mrule", "fmrule"):
                    handler_rules.append(walk_tree(child))
                elif child.type == "|":
                    # separators are added when joining handler_rules
                    pass
                elif not saw_handle:
                    handled += walk_tree(child)
                else:
                    text = walk_tree(child)
                    if text:
                        handler_rules.append(text)
            handlers_text = " | ".join(handler_rules)
            if handlers_text:
                return f"try {handled} with {handlers_text}"
            return f"try {handled}"
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
            # Match rules: join each rule with a bar
            rules: List[str] = []
            for child in node.children:
                if child.type in ("mrule", "fmrule"):
                    rules.append(walk_tree(child))
                elif child.type not in ("|", "of"):
                    text = walk_tree(child)
                    if text:
                        rules.append(text)
            return " | ".join(rules)
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
            bindings: List[str] = []
            for child in node.children:
                if child.type == "fvalbind":
                    bindings.append(walk_tree(child))
                elif child.type == "_fvalbind":
                    # Already returns a list joined with ' and '
                    bindings.append(walk_tree(child))
            return "let rec " + "\nand ".join(bindings)
        case "_fvalbind":
            # Process all fvalbind nodes, joining with 'and'
            result = ""
            first = True
            for child in node.children:
                if child.type == "fvalbind":
                    if not first:
                        result += "\nand "
                    result += walk_tree(child)
                    first = False
                elif child.type == "and":
                    pass
            return result
        case "fvalbind":
            # Contains fmrule(s) - convert multiple clauses to OCaml function syntax
            fmrules = [child for child in node.children if child.type == "fmrule"]
            
            if len(fmrules) == 1:
                # Single clause: keep simple form
                return walk_tree(fmrules[0])
            else:
                # Multiple clauses: convert to function syntax
                # SML: fun f Nil = 1 | f (Cons x) = x
                # OCaml: let rec f = function Nil -> 1 | Cons x -> x
                result = ""
                func_name = ""
                clauses = []
                
                for fmrule in fmrules:
                    children = list(fmrule.children)
                    # First child is function name (vid)
                    if children and children[0].type == "vid":
                        if not func_name:
                            func_name = walk_tree(children[0])
                        
                        # Collect patterns (between name and =)
                        pats = []
                        body = None
                        found_eq = False
                        for child in children[1:]:
                            if child.type == "=":
                                found_eq = True
                            elif not found_eq:
                                pats.append(walk_tree(child))
                            else:
                                body = walk_tree(child)
                        
                        # Single pattern can use function syntax
                        if len(pats) == 1:
                            clauses.append(f"{pats[0]} -> {body}")
                        else:
                            # Multiple patterns need tuple matching
                            pat_str = "(" + ", ".join(pats) + ")"
                            clauses.append(f"{pat_str} -> {body}")
                
                result = func_name + " = function " + " | ".join(clauses)
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
            child : TS.Node
            for child in node.children:
                if child.type == "tyvarseq":
                    result += walk_tree(child) + " "
                elif child.type == "tycon":
                    result += walk_tree(child) + " = "
                elif child.text.strip() == "=":
                    pass
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
            # SML: 'a tycon = conbind | conbind | ...
            result = ""
            conbinds = []
            
            for child in node.children:
                if child.type == "tyvarseq":
                    result += walk_tree(child) + " "
                elif child.type == "tycon":
                    result += walk_tree(child) + " = "
                elif child.type == "=":
                    pass
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
            # Flatten local blocks into sequential declarations to keep generated OCaml valid.
            prefix: List[str] = []
            body: List[str] = []
            in_body = False
            for child in node.children:
                if child.type == "in":
                    in_body = True
                elif child.type == "end":
                    break
                elif child.type.endswith("_dec"):
                    (body if in_body else prefix).append(walk_tree(child))
                elif child.type not in ("local", ";"):
                    (body if in_body else prefix).append(walk_tree(child))
            return ("\n".join(prefix + body)).strip()
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
            label = ""
            parts: list[str] = []
            for child in node.children:
                if child.type == "lab":
                    label = walk_tree(child)
                elif child.type != "=":
                    parts.append(walk_tree(child))
            value = "".join(parts)
            if " as " in value:
                value = f"({value})"
            return f"{label} = {value}" if label else value
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
                if child.type in ("(", ")", ","):
                    continue
                if child.type in ("comment", "block_comment", "line_comment"):
                    result += walk_tree(child)
                    continue
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
            parts: List[str] = []
            for child in node.children:
                parts.append(walk_tree(child))
            if parts and parts[0] == "ref" and len(parts) > 1:
                inner = " ".join(parts[1:])
                return f"{{ contents = {inner} }}"
            return " ".join(parts)
        case "typed_pat":
            # Drop type annotations inside patterns; they often introduce OCaml parsing
            # issues when translated directly from SML record patterns. Keeping only the
            # pattern improves parse success for the corpus conversion.
            result = ""
            within_type = False
            for child in node.children:
                if child.type == ":" and not within_type:
                    within_type = True
                    result += " : "
                else:
                    result += walk_tree(child)
            return result
        case "as_pat":
            # Drop aliases to avoid producing invalid OCaml patterns; keep RHS pattern
            pattern = ""
            for child in node.children:
                if child.type == "as":
                    break
                pattern += walk_tree(child)
            return pattern
        case "conj_pat":
            # Treat A as B patterns similarly by keeping only the pattern portion
            pat = ""
            for child in node.children:
                if child.type == "as":
                    break
                pat += walk_tree(child)
            return pat
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
                elif child.type in ("comment", "block_comment", "line_comment"):
                    result += walk_tree(child)
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
            # OCaml lacks anonymous record type expressions; map to an object type
            # so field names remain visible and the parser accepts inline usages.
            fields = []
            for child in node.children:
                if child.type in ("{", "}", ","):
                    continue
                fields.append(walk_tree(child))
            return "<" + "; ".join(fields) + ">"
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
                if child.type == "tyseq":
                    result += walk_tree(child) + " "
                elif child.type not in ("(", ")"):
                    result += walk_tree(child)
            return result.rstrip()
        
        # Structure/Module expressions
        case "struct_strexp":
            result = "struct "
            for child in node.children:
                if child.type == "struct":
                    pass
                elif child.type == "end":
                    result += " end"
                    break
                elif child.type != ";":
                    result += walk_tree(child) + "\n"
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
            # SML: Fct (structure A = ... structure B = ...) -> OCaml: Fct (struct module A = ... end) (struct module B = ... end)
            result = ""
            args: List[str] = []
            for child in node.children:
                if child.type == "fctid":
                    result += walk_tree(child)
                elif child.type in ("structure_strdec", "sigexp", "strexp"):
                    arg_text = walk_tree(child).strip()
                    if child.type == "structure_strdec" and not arg_text.startswith("struct"):
                        arg_text = f"struct {arg_text} end"
                    args.append(arg_text)
            for arg in args:
                result += f" ({arg})"
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
                elif child.type == ":":
                    result += " : "
                elif child.type == ":>":
                    # Opaque signature constraint - convert to regular constraint in OCaml
                    result += " : "
                elif child.type == "=":
                    result += " = "
                elif child.type not in ("strid", ":", ":>", "="):
                    result += walk_tree(child)
            return result
        case "local_strdec":
            prefix: List[str] = []
            body: List[str] = []
            in_body = False
            for child in node.children:
                if child.type == "in":
                    in_body = True
                elif child.type == "end":
                    break
                elif child.type.endswith("_dec"):
                    (body if in_body else prefix).append(walk_tree(child))
                elif child.type != ";":
                    (body if in_body else prefix).append(walk_tree(child))
            return ("\n".join(prefix + body)).strip()
        
        # Signature expressions
        case "sig_sigexp":
            result = "sig\n"
            for child in node.children:
                if child.type == "sig":
                    pass
                elif child.type == "end":
                    result += "\nend"
                    break
                elif child.type == ";":
                    result += "\n"
                elif child.type.endswith("_spec"):
                    text = walk_tree(child)
                    if text:
                        result += "  " + text + "\n"
                else:
                    text = walk_tree(child)
                    if text:
                        result += text
            return result
        case "sigid_sigexp":
            return walk_children(node)
        case "wheretype_sigexp":
            # SML: sigexp where type ... = ... -> OCaml: sigexp with type ... = ...
            result = ""
            for child in node.children:
                if child.type == "where":
                    result += " with "
                elif child.type == "type":
                    result += "type "
                elif child.type == "=":
                    result += " = "
                else:
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
                if child.type == "tyvarseq":
                    result += walk_tree(child) + " "
                elif child.type == "tycon":
                    result += walk_tree(child)
                elif child.type not in ("=", "and"):
                    result += walk_tree(child)
            return result
        case "datdesc":
            # datatype name = conbind | conbind in signature
            result = ""
            condescs = []
            
            for child in node.children:
                if child.type == "tyvarseq":
                    result += walk_tree(child) + " "
                elif child.type == "tycon":
                    result += walk_tree(child) + " = "
                elif child.type == "=":
                    pass
                elif child.type == "condesc":
                    condescs.append(child)
            
            # Process all condesc, joining with ' | '
            for i, condesc in enumerate(condescs):
                if i > 0:
                    result += " | "
                result += walk_tree(condesc)
            
            return result
        case "condesc":
            # Constructor description in signature (like conbind)
            result = ""
            for child in node.children:
                if child.type == "vid":
                    result += walk_tree(child)
                elif child.type == "of":
                    result += " of "
                elif child.type not in ("vid", "of", "|"):
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
            # OCaml functor syntax: module name (Arg1 : SIG1) (Arg2 : SIG2) : OUT = body
            result = ""
            in_params = False
            params = []
            for child in node.children:
                if child.type == "fctid":
                    result += walk_tree(child)
                elif child.type == "(":
                    in_params = True
                elif child.type == ")":
                    in_params = False
                    # Output all collected params
                    for p in params:
                        result += " (" + p + ")"
                    params = []
                elif child.type in (":", ":>", "="):
                    # OCaml uses a plain ':' for both transparent and opaque specs here
                    op = ":" if child.type in (":", ":>") else "="
                    result += f" {op} "
                elif child.type == "structure_spec" and in_params:
                    # Functor parameter: structure Name : SIG
                    strdesc = None
                    for c in child.children:
                        if c.type == "strdesc":
                            strdesc = c
                    if strdesc:
                        name = ""
                        sig = ""
                        for c in strdesc.children:
                            if c.type == "strid":
                                name = walk_tree(c)
                            elif c.type == "sigid_sigexp":
                                sig = walk_tree(c)
                        if name and sig:
                            params.append(f"({name} : {sig})")
                elif child.type == "sharing_spec" and in_params:
                    # Skip sharing constraints in parameters
                    pass
                elif child.type in ("block_comment", "line_comment"):
                    # Skip comments in parameters
                    pass
                elif child.type != "fctid":
                    text = walk_tree(child)
                    if text:
                        # ensure a space before a result signature if it immediately follows params
                        if not result.endswith(" "):
                            result += " "
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
        # Prepare to insert helper functions soon