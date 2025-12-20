"""
Corpus test: ensure files in `examples/sml_sources/` convert to parsable OCaml.
"""

import unittest
from pathlib import Path
import sys

# Setup path for imports
ROOT_DIR = Path(__file__).resolve().parents[1]
PY_BINDINGS = ROOT_DIR / "python" / "tree_sitter_sml"
SRC_DIR = ROOT_DIR / "src"
if str(PY_BINDINGS) not in sys.path:
    sys.path.append(str(PY_BINDINGS))
if str(SRC_DIR) not in sys.path:
    sys.path.append(str(SRC_DIR))

from test_ocaml import test_ocaml_code
from sml_process import process_code, PARSER as SML_PARSER
import tree_sitter as TS
VERBOSE = False
class TestCorpusFiles(unittest.TestCase):
    """Validate conversion of all files in the sml_sources folder."""

    def test_all_sml_like_files_parse_in_ocaml(self):
        base_dir = ROOT_DIR / "examples" / "sml_sources"
        allowed_exts = {".sml", ".sig", ".fun"}
        if VERBOSE is False:
                    failures_dir = ROOT_DIR / "test_suite" / "failures"
                    if failures_dir.exists():
                        for f in failures_dir.iterdir():
                            f.unlink() 
                        failures_dir.rmdir()
        for path in base_dir.rglob("*"):
            if path.is_file() and path.suffix in allowed_exts:
                
                with self.subTest("Testing ${path}",file=str(path)):
                    text = path.read_text(encoding="utf-8", errors="ignore")
                    converted = process_code(text)
                    
                    # Parse both SML and OCaml for error reporting
                    sml_tree = SML_PARSER.parse(text.encode("utf-8"))
                    ocaml_result = test_ocaml_code(converted)
                    
                    if isinstance(ocaml_result, TS.Tree):
                        self.assertTrue(True)
                    else:
                        # Format failure message with all requested information
                        failure_msg = f"""
================================================================================
FILE: {path}
================================================================================

SML SOURCE:
--------------------------------------------------------------------------------
{text}
================================================================================

CONVERTED OCaml:
--------------------------------------------------------------------------------
{converted}
================================================================================

SML PARSE TREE:
--------------------------------------------------------------------------------
{sml_tree.root_node}
================================================================================

OCaml PARSE TREE:
--------------------------------------------------------------------------------
"""
                        # Parse the OCaml code to show parse tree
                        try:
                            from tree_sitter import Language, Parser
                            import tree_sitter_ocaml
                            ocaml_lang = Language(tree_sitter_ocaml.language_ocaml())
                            ocaml_parser = Parser(ocaml_lang)
                            ocaml_tree = ocaml_parser.parse(converted.encode("utf-8"))
                            failure_msg += str(ocaml_tree.root_node)
                        except Exception as e:
                            failure_msg += f"(Could not parse: {path})"
                        
                        failure_msg += "\n================================================================================"
                        if VERBOSE == 1 or VERBOSE is True:
                            self.fail(failure_msg)
                        elif VERBOSE == 0 or VERBOSE is False:
                            
                            # Save failed output to a file for later inspection
                            failures_dir = ROOT_DIR / "test_suite" / "failures"
                            
                            # TODO remove if exists
                            failures_dir.mkdir(exist_ok=True)
                            
                            ocaml_suffix = ".ml"
                            if path.suffix == ".sig":
                                ocaml_suffix = ".mli"

                            failure_file = failures_dir / f"{path.stem}{ocaml_suffix}"
                            fail_file = converted + "\n\n(** NOTE SML SOURCE \n" + text + "\n**)\n"
                            failure_file.write_text(fail_file, encoding="utf-8")
                            self.fail(f"Conversion failed for file: {path}. Run with VERBOSE=True for details.")
                            # Create `failures` directory if it doesn't exist

if __name__ == "__main__":
    unittest.main(verbosity=0)
    print("All tests passed!")
