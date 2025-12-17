# SML-to-OCaml Converter: AI Agent Instructions

## Architecture Overview

This project is a **tree-sitter-based AST converter** that transforms SML code to OCaml. The core pattern is:
1. **Parse**: tree-sitter-sml grammar parses SML code into an Abstract Syntax Tree (AST)
2. **Walk**: Recursive descent traversal via `walk_tree()` function
3. **Convert**: Pattern-match on `node.type` to apply SML→OCaml transformation rules
4. **Validate**: Parse generated OCaml with tree-sitter-ocaml to verify syntax

**Key insight**: The converter handles ~1200 node types. Each handler is responsible for:
- Skipping anonymous grammar rules (prefixed `_`, like `_exp`, `_pat`)
- Collecting like-minded children (e.g., multiple `valbind` nodes)
- Joining with appropriate separators (`and`, `|`, `;`, `,`)
- Outputting proper OCaml syntax

## Critical File: `src/sml_process.py`

**Structure** (1171 lines):
- Lines 1-50: Imports and tree-sitter setup
- Lines 52-1171: `walk_tree()` match statement with ~120 case handlers

**Common patterns in handlers:**

```python
# Pattern 1: Collect and join (for multi-item declarations)
case "val_dec":
    valbinds = [walk_tree(c) for c in node.children if c.type == "valbind"]
    return "let " + " and ".join(valbinds)  # Join with ' and '

# Pattern 2: Skip separators, collect content
case "tuple_exp":
    items = [walk_tree(c) for c in node.children if c.type not in ("(", ")", ",")]
    return "(" + ", ".join(items) + ")"

# Pattern 3: Manual child iteration with context
case "strbind":
    result = ""
    for child in node.children:
        if child.type == "strid": result += walk_tree(child)
        elif child.type == "=": result += " = "
        elif not child.type.endswith("_"): result += walk_tree(child)
    return result
```

## Testing & Validation

**Current metrics** (as of Dec 2025): **429 failures, 39 passing (8.3% pass rate)**

**Test files**:
- `test_suite/test_corpus.py` - Runs all 468 SML files, counts passes/fails
- `test_suite/test_ocaml.py` - Validates OCaml syntax using tree-sitter-ocaml query for ERROR/MISSING nodes
- `examples/sml_sources/` - 468 SML test files organized by module (compat/, compile/, etc.)

**Run tests**:
```bash
timeout 120 python test_suite/test_corpus.py  # Full suite (468 files)
python test_suite/test_corpus.py 2>&1 | grep "^ok"  # List passing tests
```

**Debug strategy**:
```python
from src.sml_process import process_code
from test_suite.test_ocaml import test_ocaml_code

code = "val x = 5"  # Test code
result = process_code(code)  # SML→OCaml
is_valid = test_ocaml_code(result)  # Validate syntax
```

## Known Limitations & Grammar Issues

**Blocker**: tree-sitter-sml grammar has gaps. Common failure modes:

1. **Module functors with named arguments**: `Compat(module Array = Array)` parses as ERROR
2. **Module type declarations**: `module type T = sig ... end` not properly parsed
3. **Complex signatures**: Some `sig ... end` blocks with type specs cause parse failures
4. **Comments disrupting grammar**: Some files with specific comment placement fail to parse

**Workaround for grammar issues**: If grammar fails, ERROR nodes are returned; current handler outputs raw text, preventing full conversion.

## Key Conversion Rules (NOT exhaustive - see code for all ~120)

| SML | OCaml | Handler |
|-----|-------|---------|
| `val x = e` | `let x = e` | `val_dec` (line ~405) |
| `fun f x = e` | `let rec f x = e` | `fun_dec` (line ~461) |
| `[a, b]` | `[a; b]` | `list_exp` (line ~203) |
| `(a, b)` | `(a, b)` | `tuple_exp` (line ~187) |
| `{a=1, b=2}` | `{a = 1; b = 2}` | `record_exp` (line ~143) |
| `e1 andalso e2` | `e1 && e2` | `conj_exp` (line ~290) |
| `structure S = ...` | `module S = ...` | `structure_strdec` (line ~898) |
| `e handle E => e'` | `try e with E -> e'` | `handle_exp` (line ~335) |

## Recent Fixes (Session Dec 2025)

1. **Tuple comma duplication** - Skip commas in tuple_exp/tuple_pat to avoid `(a, , s)`
3. **Declaration separation** - `source_file` and `sig_sigexp` now insert newlines between items
4. **ERROR handling** - Added case for ERROR nodes to output raw text

## Development Workflow

**To add a new handler or fix an existing one:**

1. **Understand the node structure**: Use the parser to see AST shape:
   ```python
   from tree_sitter import Language, Parser
   parser = Parser(Language(tree_sitter_sml.language()))
   tree = parser.parse(b"val x = 5")
   # Inspect tree.root_node.children recursively
   ```

2. **Check for anonymous rules**: If grammar has `_ exp` rule, it inlines children (no `_exp` node)

3. **Test isolated**: Write minimal test case in `test_ocaml_code()` before running full suite

4. **Watch for separator tokens**: Commas, pipes, `and` keywords are separate nodes - handle in parent, not child

5. **Run full suite sparingly**: `timeout 120` prevents hangs on complex files

## Dependencies

**Python packages**:
- `tree-sitter` (parser infrastructure)
- `tree-sitter-ocaml` (OCaml syntax validation)
- `tree_sitter_sml` (included in `python/tree_sitter_sml/`, pre-compiled)

**Installation**:
```bash
pip install tree-sitter tree-sitter-ocaml
# tree_sitter_sml is local; no pip install needed
```

## Project Context

This converter exists to **translate Twelf's SML codebase to OCaml** as part of broader compiler modernization. The ~468 SML source files in `examples/sml_sources/` represent real Twelf code (modules, signatures, functors, complex types).

The 8.3% pass rate reflects grammar limitations, not converter design - simple files convert perfectly; complex module syntax fails at parse stage.
