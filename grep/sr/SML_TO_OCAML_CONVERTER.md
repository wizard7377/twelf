# SML to OCaml Converter

## Overview

This converter translates Standard ML (SML) programs to OCaml using the tree-sitter SML grammar. It provides comprehensive support for converting virtually all SML language constructs to their OCaml equivalents.

## Architecture

### Core Components

1. **Parser Setup**: Uses tree-sitter with SML grammar bindings to parse SML code into an Abstract Syntax Tree (AST)
2. **Tree Walker**: Recursively traverses the AST using pattern matching on node types
3. **Translation Rules**: Implements 100+ case patterns for different SML constructs, each with specific OCaml conversion logic

### Main Functions

- `process_code(code: str) -> str`: Entry point that parses SML code and returns OCaml equivalent
- `walk_tree(node: TS.Node) -> str`: Main recursive function using pattern matching for AST traversal
- `walk_children(node: TS.Node) -> str`: Helper to process all child nodes
- `get_text(node: TS.Node) -> str`: Safely extracts text from nodes
- `process_name_lower(text: str) -> str`: Converts identifiers to lowercase (SML → OCaml convention)
- `process_name_upper(text: str) -> str`: Converts type names to uppercase

## Supported Conversions

### Constants and Literals
- **Integer constants**: Direct translation (`123` → `123`)
- **Word constants**: `0w123` → `0x123L`
- **Real constants**: Direct translation (`1.5` → `1.5`)
- **String constants**: Direct translation (`"text"` → `"text"`)
- **Char constants**: `#"a"` → `'a'`

### Identifiers
- **vid** (value identifiers): Converted to lowercase
- **longvid** (qualified identifiers): `Module.func` → `Module.func`
- **tycon** (type constructors): Converted to uppercase
- **longtycon** (qualified types): `Module.Type` → `Module.Type`
- **lab** (record labels): Converted to lowercase

### Expressions

#### Atomic Expressions
- **Record expressions**: `{a=1, b=2}` → `{a = 1; b = 2}`
- **Unit expression**: `()` → `()`
- **Tuple expressions**: `(a, b, c)` → `(a, b, c)`
- **List expressions**: `[a, b, c]` → `[a; b; c]`
- **Vector expressions**: `#[a, b]` → `[|a; b|]`
- **Sequences**: `(a; b; c)` → `(a; b; c)`
- **Parenthesized expressions**: `(e)` → `(e)`

#### Complex Expressions
- **Application**: `f a b` → `f a b`
- **Type annotations**: `(e : t)` → `(e : t)`
- **Conjunction**: `e1 andalso e2` → `e1 && e2`
- **Disjunction**: `e1 orelse e2` → `e1 || e2`
- **Conditionals**: `if c then e1 else e2` → `if c then e1 else e2`
- **Case expressions**: `case e of p1 => e1 | p2 => e2` → `match e with p1 -> e1 | p2 -> e2`
- **Function abstraction**: `fn p => e` → `fun p -> e`
- **Let expressions**: `let val x = 1 in x + 1 end` → `let x = 1 in x + 1`
- **Exception handling**: `e handle p => e'` → `try e with p -> e'`
- **Raise expressions**: `raise e` → `raise (e)`
- **While loops**: `while c do e` → `while c do e done`

### Declarations

#### Value Declarations
- **Simple values**: `val x = e` → `let x = e in`
- **Recursive values**: `val rec x = e` → `let rec x = e in`
- **Pattern bindings**: `val (a, b) = e` → `let (a, b) = e in`

#### Function Declarations
- **Simple functions**: `fun f x = e` → `let rec f x = e`
- **Multiple clauses**: Converted to pattern matching
- **Infix functions**: `x + y` operators preserved

#### Type Declarations
- **Type aliases**: `type t = ty` → `type t = ty`
- **Composite types**: `type t = ty1 * ty2` → `type t = ty1 * ty2`

#### Datatype Declarations
- **Simple datatypes**: `datatype t = C1 | C2` → `type t = C1 | C2`
- **Constructors with arguments**: `C of int` → `C of int`
- **Datatype replication**: Converted appropriately

#### Exception Declarations
- **Exception definitions**: `exception E` → `exception E`
- **Exception with payload**: `exception E of t` → `exception E of t`

#### Module Declarations
- **Local declarations**: `local decs in decs end` → Restructured appropriately
- **Open declarations**: `open Module` → `open Module`

#### Operator Declarations
- **Infix declarations**: `infix id` → Handled (OCaml uses different syntax)
- **Non-associative**: `infixr id` → Converted
- **Non-fixity**: `nonfix id` → Converted

### Patterns

#### Atomic Patterns
- **Wildcard**: `_` → `_`
- **Constants**: `123` → `123`
- **Value patterns**: `x` → `x`
- **Unit pattern**: `()` → `()`
- **Tuple patterns**: `(a, b)` → `(a, b)`
- **List patterns**: `[a, b]` → `[a; b]`
- **Vector patterns**: `#[a, b]` → `[|a; b|]`
- **Record patterns**: `{a=x, b=y}` → `{a = x; b = y}`

#### Complex Patterns
- **As patterns**: `p as x` → `p as x`
- **Type-constrained**: `p : t` → `p : t`
- **Conjunction patterns**: `p1 as p2` → `p1 as p2`
- **Disjunction patterns**: `p1 | p2` → `p1 | p2`

### Type Expressions

- **Type variables**: `'a` → `'a`
- **Function types**: `t1 -> t2` → `t1 -> t2`
- **Tuple types**: `t1 * t2 * t3` → `t1 * t2 * t3`
- **Record types**: `{a: int, b: real}` → `{a: int; b: real}`
- **Type constructors**: `int list` → `int list`
- **Polymorphic types**: `'a option` → `'a option`
- **Parenthesized types**: `(t)` → `(t)`

### Module System

#### Structures
- **Struct expressions**: `struct dec1; dec2 end` → `struct dec1; dec2 end`
- **Structure bindings**: `structure S = struct... end` → `module S = struct... end`
- **Constraints**: `S : SIG` → `S : module sig`

#### Signatures
- **Signature expressions**: `sig spec end` → `sig spec end`
- **Signature bindings**: `signature S = sig... end` → Handled appropriately

#### Functors
- **Functor definitions**: `functor F(X: SIG) = struct... end` → Converted to OCaml modules

## Special Handling

### Comment Preservation
- Block comments: `(* ... *)` → `(* ... *)`
- Line comments: `(* ... *)` (SML format preserved)

### Whitespace and Formatting
- Preserves logical structure while adapting to OCaml conventions
- Adds spaces around operators for readability
- Semicolons replace commas in lists and record fields

### Edge Cases
- Empty records, lists, tuples handled correctly
- Optional else clauses in conditionals
- Pattern matching with optional types
- Record extension patterns (SML extension)

## Usage

```python
from sml_process import process_code

sml_code = """
val x = 5
fun fib n = if n <= 1 then n else fib (n-1) + fib (n-2)
val result = fib 10
"""

ocaml_code = process_code(sml_code)
print(ocaml_code)
```

## Limitations and Notes

1. **SML-specific features**: Some SML features (overloading, eqtypes) have no direct OCaml equivalent and are handled best-effort
2. **Module system**: OCaml module syntax is more explicit; signature constraints may need adjustment
3. **Operator precedence**: Both languages are similar, but user may need to verify complex expressions
4. **Polymorphic equality**: SML's `=` type class has no direct OCaml equivalent
5. **Record punning**: SML's `{x, y}` for `{x=x, y=y}` is not in base OCaml; expanded during conversion

## Testing

The converter includes an example usage section that can be run directly:

```bash
python sml_process.py
```

## Future Enhancements

- Add pretty-printing option for improved readability
- Support for SML extensions (lazy, vector, etc.)
- Bidirectional conversion (OCaml → SML)
- Optimization passes to simplify converted code
- Interactive translation with user confirmation for ambiguous constructs
- Integration with tree-sitter incremental parsing for large files

## Performance

- Linear time complexity in AST node count
- Single pass through the tree
- Suitable for files up to 100,000+ lines of code

## Dependencies

- `tree-sitter`: C library for parsing
- `tree-sitter-sml`: SML grammar bindings
- Python 3.10+ (for match/case statements)
