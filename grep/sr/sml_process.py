"""Process SML to OCaml using tree-sitter SML grammar."""

import grammar
# NOTE: Refer back to `grammar.js` for the Tree Sitter Grammar 
from pathlib import Path
import sys

from tree_sitter import Language, Parser
import tree_sitter as TS
# Ensure the local Python binding is importable when the package isn't installed.
ROOT_DIR = Path(__file__).resolve().parents[1]
PY_BINDINGS = ROOT_DIR / "ts" / "bindings" / "python"
if str(PY_BINDINGS) not in sys.path:
    sys.path.append(str(PY_BINDINGS))

import tree_sitter_sml

SML_LANGUAGE : Language = Language(tree_sitter_sml.language())
PARSER : Parser = Parser(SML_LANGUAGE)


def process_code(code: str) -> str:
    # Parse to validate the input as SML; tree-sitter returns a tree even for partial parses.
    
    tree : TS.Tree = PARSER.parse(code.encode("utf-8"))
    cursor = tree.walk()
    res : str = walk_tree(cursor)
    # Placeholder: return the original code until OCaml translation is implemented.
    return res

    """Make Name correct Ocaml

    """
def process_name_lower(name: TS.Node) -> str:
    sname : str = cursor.node.text;
    return sname[0].lower() + sname[1:]
def process_name_upper(name: TS.Node) -> str:
    sname : str = cursor.node.text;
    return sname[0].upper() + sname[1:]

def walk_simple(cursor : TS.TreeCursor) -> str:
    node = cursor.node
    curStr : str = ""
    for child in node.children:
        curStr += walk_tree(child.walk())
    return curStr
def walk_tree(cursor : TS.TreeCursor) -> str: 
    match cursor.node.type:
        case "source_file":
            cursor.goto_first_child();
            return walk_tree(cursor)
        case "comment":
            return cursor.node.text
        case "vid" :
            return process_name_lower(cursor.node.text)
        case "longvid" :
            node = cursor.node
            curStr : str = ""
            for child in node.children[:-1]:
                curStr += child.text + "."
            curStr += process_name_lower(node.children[-1].text)
            return curStr
        case "tycon":
            return process_name_upper(cursor.node.text)
        case "longtycon":
            node = cursor.node
            curStr : str = ""
            for child in node.children[:-1]:
                curStr += child.text + "."
            curStr += process_name_upper(node.children[-1].text)
            return curStr
        case "lab": 
            return process_name_lower(cursor.node.text)
        case "scon_exp":
            cursor.goto_first_child();
            return walk_tree(cursor)
        case "vid_exp":
            return walk_simple(cursor)
        case "record_exp":
            
        

         


    