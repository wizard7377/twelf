# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Project Overview

This is an OCaml port of the [Twelf Project](http://twelf.org/), originally implemented in Standard ML. Twelf is:
- An implementation of the LF logical framework with type reconstruction
- The Elf constraint logic programming language
- A meta-theorem prover for LF
- A set of expansion modules for numbers and strings

The port preserves the original SML architecture while adapting it to OCaml idioms.

## Build Commands

This project uses Dune as the build system with several build profiles:

```bash
# Build (release profile)
make build
# or: dune build --profile release

# Build with strict checking (recommended for development)
make check
# or: dune build --profile check

# Build with warnings disabled (for working with legacy code)
make sane
# or: dune build --profile sane

# Run tests
make test
# or: dune runtest

# Build documentation
make doc
# or: dune build @doc

# Launch REPL
make repl
# or: dune utop

# Clean build artifacts
make clean
# or: dune clean
```

**Build Profile Notes:**

- `check` - Most strict, recommended for new development
- `sane` - Disables warnings (`-w -A`), useful when working with ported SML code that may have style issues
- `dev` - Standard OCaml warnings
- `release` - Optimized production build

## Architecture

### Library Organization

The codebase is organized into ~44 library modules under `lib/`, each handling a specific concern. The main library is defined in `lib/dune` with modules organized as follows:

**Core Foundation:**
- `basis/`: SML compatibility layer providing modules like Array, List, Vector, Integer, TextIO, Time, etc. This is a wrapped library that bridges SML idioms to OCaml. Depends on the `mtime` library.

**Logical Framework Core:**
- `lambda/`: Lambda calculus representation
- `typecheck/`: Type checking for LF
- `index/`: Indexing for efficient lookup
- `print/`: Pretty printing for terms and types
- `subordinate/`: Subordination relation between type families
- `names/`: Name management

**Compilation and Optimization:**
- `compile/`: Compilation of LF to abstract machine
- `compress/`: Term compression
- `table/`: Hash tables and data structures (includes sparse arrays)

**Meta-Reasoning:**
- `modes/`: Mode checking for relations
- `terminate/`: Termination checking
- `cover/`: Coverage checking
- `prover/`: Automated theorem prover
- `tabling/`: Tabled logic programming
- `thm/`: Theorem declarations and management
- `worldcheck/`: World checking for theorems

**Frontend and I/O:**
- `frontend/`: Parser and top-level interface
- `formatter/`: Formatting utilities
- `stream/`: Stream processing
- `msg/`: Message and error handling
- `paths/`: File path handling

**Advanced Features:**
- `modules/`: Module system
- `delphin/`: Delphin functional programming extension
- `m2/`: Meta-level 2 reasoning
- `tomega/`: Termination ordering (Ω)
- `flit/`: FLit language support
- `solvers/`: Constraint solvers
- `opsem/`: Operational semantics
- `domains/`: Abstract domains
- `unique/`: Uniqueness checking
- `meta/`: Meta-variables and constraints

**Infrastructure:**
- `global/`: Global parameters and configuration
- `timing/`: Performance timing
- `trail/`: Backtracking trail for search
- `server/`: Twelf server functionality
- `netserver/`: Network server

**Style and Formatting:**
- `style/`: Style checking and formatting
- `order/`: Ordering relations
- `heuristic/`: Heuristics for proof search

### Binary Structure

- `bin/`: Main executable (`twelf`) that depends on `basis` and `twelf` libraries
- `bin_old/`: Legacy binary (deprecated)

### Naming Conventions

The original SML code follows these conventions (preserved in the port):
- `<function>` - general function
- `<function>W` - expects weak head-normal form
- `<function>N` - expects normal form

## SML to OCaml Port Considerations

This is an ongoing port from Standard ML to OCaml. When working on this codebase:

### Porting Guidelines

1. **Basis Library**: The `lib/basis/` module provides SML-compatible interfaces. When adding SML features, extend this module rather than using OCaml stdlib directly in ported code.

2. **Module Structure**: Each library subdirectory typically contains:
   - `dune` - Build configuration
   - `*.ml` - Implementation files
   - `*.mli` - Interface files (when present)
   - `README` or `WALK` - Original documentation (legacy)

3. **Build Profiles**: Use `check` profile for strict checking during new development. Use `sane` when working with legacy ported code that has warning issues.

### Active Port Tasks (see `org/ocaml.org`)

**Tooling Migration:**

- ML Yacc → Menhir (in progress)
- ML Lex → OCamllex (in progress)
- Documentation → odoc style

**Code Modernization:**

- Convert functions to curried style (OCaml idiom)
- Rename identifiers that clash with OCaml keywords (e.g., `module_` should get better names)
- Remove unnecessary `let rec` where `let` suffices
- Follow OCaml naming conventions and style guide
- Add parentheses for readability where needed

**Dune Improvements:**

- Fix module wrapping issues
- Make module system more OCaml-like
- Improve makefile to be more idiomatic

**Future Enhancements:**

- REPL improvements for Twelf server
- LSP integration for editor support
- Pretty printing improvements

## Testing

Tests are located in `test/`. The test suite can be run with:
```bash
dune runtest
```

The original Twelf test suite is in `test/TEST/` (Makefile-based, may need adaptation).

## CI/CD

The project uses GitHub Actions (`.github/workflows/ocaml-ci.yml`) and tests on:
- OCaml versions: 4.x and 5.x
- Platforms: Ubuntu, macOS, Windows

Each CI run executes:
1. `opam install . --deps-only --with-test`
2. `dune build`
3. `dune runtest`
4. `dune build @doc`

## Documentation

- Generated documentation: `_build/default/_doc/_html/index.html` (after `make doc`)
- Original Twelf documentation: `old_doc/` (outdated but may provide context)
- Examples: `examples/`, `examples-clp/`, `examples-delphin/`
- Project website: http://twelf.org/

## File Organization

- `lib/WALK` - Historical file from original codebase with architectural notes
- `HISTORY` - Change log from original Twelf project
- `TODO_OLD` - Historical TODO items from SML version
- `README_OLD.md` - Original Twelf README
- `.ocamlformat` - OCaml formatting configuration
