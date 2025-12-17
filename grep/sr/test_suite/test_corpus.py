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
from sml_process import process_code

class TestCorpusFiles(unittest.TestCase):
    """Validate conversion of all files in the sml_sources folder."""

    def test_all_sml_like_files_parse_in_ocaml(self):
        base_dir = ROOT_DIR / "examples" / "sml_sources"
        allowed_exts = {".sml", ".sig", ".fun"}
        for path in base_dir.rglob("*"):
            if path.is_file() and path.suffix in allowed_exts:
                with self.subTest("Testing ${path}",file=str(path)):
                    text = path.read_text(encoding="utf-8", errors="ignore")
                    converted = process_code(text)
                    #print("Original:\n" + text)
                    #print("Converted:\n" + converted)
                    res = test_ocaml_code(converted)
                    if res == True:
                        self.assertTrue(True)
                    else:
                        print(res)
                        self.fail("Failed to parse in OCaml: " + str(path))
                        
                        

if __name__ == "__main__":
    unittest.main()
