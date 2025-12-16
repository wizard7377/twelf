"""Process SML to OCaml using tree-sitter SML grammar."""

from pathlib import Path
import sys

from tree_sitter import Language, Parser

# Ensure the local Python binding is importable when the package isn't installed.
ROOT_DIR = Path(__file__).resolve().parents[1]
PY_BINDINGS = ROOT_DIR / "ts" / "bindings" / "python"
if str(PY_BINDINGS) not in sys.path:
    sys.path.append(str(PY_BINDINGS))

import tree_sitter_sml

SML_LANGUAGE = Language(tree_sitter_sml.language())
PARSER = Parser(SML_LANGUAGE)


def process_code(code: str) -> str:
    # Parse to validate the input as SML; tree-sitter returns a tree even for partial parses.
    PARSER.parse(code.encode("utf-8"))
    # Placeholder: return the original code until OCaml translation is implemented.
    return code