# grep/sr Directory Reorganization Summary

## Changes Made

The `grep/sr` directory has been reorganized for better structure and clarity. All files have been moved to appropriate subdirectories based on their purpose.

## New Directory Structure

```
grep/sr/
├── 📄 Documentation Files
│   ├── README.md                    # Main documentation (updated)
│   ├── INSTALL.md                   # Installation guide (NEW)
│   ├── QUICKSTART.md                # Quick reference guide (NEW)
│   ├── SML_TO_OCAML_CONVERTER.md   # Detailed converter documentation
│   ├── INDEX.md                     # Project index
│   └── COMPLETION_SUMMARY.md        # Implementation summary
│
├── 📂 src/                          # Core converter modules (NEW)
│   ├── sml_process.py              # Main converter (moved from root)
│   ├── grammar.py                  # Grammar utilities (moved from root)
│   ├── grammar.js                  # Tree-sitter grammar (moved from root)
│   ├── main.py                     # CLI interface (moved from root)
│   └── __init__.py                 # Package init (NEW)
│
├── 📂 test_suite/                   # All test files (NEW)
│   ├── test_converter.py           # Main tests (moved from root)
│   ├── test_ocaml.py               # OCaml tests (moved from root)
│   ├── test_corpus.py              # Corpus tests (moved from python/tests/)
│   └── __init__.py                 # Package init (NEW)
│
├── 📂 examples/                     # Examples and test data
│   ├── examples.py                 # Demo programs (moved from root)
│   ├── __init__.py                 # Package init (NEW)
│   └── sml_sources/                # SML test sources (moved from test/)
│       ├── compat/
│       ├── compile/
│       ├── compress/
│       └── ... (42 more directories with SML files)
│
├── 📂 python/                       # Tree-sitter SML bindings (unchanged)
│   └── tree_sitter_sml/
│
└── 📄 Configuration Files
    ├── Pipfile                      # Python dependencies
    └── Pipfile.lock                 # Locked dependencies
```

## Files Moved

### To `src/` directory:
- `main.py` → `src/main.py`
- `sml_process.py` → `src/sml_process.py`
- `grammar.py` → `src/grammar.py`
- `grammar.js` → `src/grammar.js`

### To `test_suite/` directory:
- `test_converter.py` → `test_suite/test_converter.py`
- `test_ocaml.py` → `test_suite/test_ocaml.py`
- `python/tests/test_corpus.py` → `test_suite/test_corpus.py`

### To `examples/` directory:
- `examples.py` → `examples/examples.py`
- `test/*` → `examples/sml_sources/*` (all SML test files)

## New Files Created

1. **`INSTALL.md`** - Comprehensive installation guide with:
   - Required dependencies (tree-sitter, tree-sitter-ocaml)
   - Multiple installation methods (pip, pipenv, requirements.txt)
   - Verification steps
   - Troubleshooting guide

2. **`QUICKSTART.md`** - Quick reference guide with:
   - Directory structure overview
   - Quick start commands
   - Usage examples
   - Key requirements summary

3. **`src/__init__.py`** - Makes src a Python package
4. **`test_suite/__init__.py`** - Makes test_suite a Python package
5. **`examples/__init__.py`** - Makes examples a Python package

## Updated Files

### `README.md`
- Updated directory structure documentation
- Updated installation section to highlight required dependencies
- Updated all usage examples to reflect new paths
- Updated contributing guide with new file locations

### `QUICKSTART.md`
- Updated directory structure
- Updated all example commands

### Import statements updated in:
- `test_suite/test_converter.py` - Updated imports for new structure
- `test_suite/test_corpus.py` - Updated paths to find sml_sources in examples/
- `examples/examples.py` - Updated imports for new structure
- `src/main.py` - Updated imports for new structure

## Installation Requirements Documented

The following dependencies **must** be installed:

1. **tree-sitter** - Python bindings for tree-sitter parser
   ```bash
   pip install tree-sitter
   ```

2. **tree-sitter-ocaml** - OCaml language support for tree-sitter
   ```bash
   pip install tree-sitter-ocaml
   ```

These requirements are now prominently documented in:
- `README.md` (Installation section)
- `INSTALL.md` (Complete installation guide)
- `QUICKSTART.md` (Quick reference)

## Benefits of Reorganization

1. **Better Organization**: Core code, tests, and examples are clearly separated
2. **Clearer Dependencies**: Installation requirements are prominently documented
3. **Easier Navigation**: Logical directory structure makes finding files easier
4. **Proper Python Packaging**: All directories are proper Python packages
5. **Better Documentation**: Multiple documentation files for different needs
6. **Consistent Structure**: Follows standard Python project conventions

## Testing

After reorganization, tests can be run with:

```bash
# Run all tests
python -m unittest discover -s test_suite -p "test_*.py" -v

# Run specific test files
python -m unittest test_suite.test_converter -v
python -m unittest test_suite.test_corpus -v
python -m unittest test_suite.test_ocaml -v
```

## Running Examples

```bash
python examples/examples.py
```

## Using the CLI

```bash
python src/main.py input.sml output.ml
```

## Migration Notes

If you have existing scripts that import from the old structure:

**Old:**
```python
from sml_process import process_code
```

**New:**
```python
from src.sml_process import process_code
```

Or add the src directory to your path:
```python
import sys
from pathlib import Path
sys.path.append(str(Path(__file__).parent / "src"))
from sml_process import process_code
```
