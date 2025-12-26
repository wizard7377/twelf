---
name: currying-functions
description: Transform uncurried functions to curried functions in OCaml (project)
---

# Currying Functions in the Twelf OCaml Port

This skill converts SML-style uncurried functions to idiomatic OCaml curried style.

## What This Does

Transforms function definitions and call sites from tuple-based arguments to curried form:

**Function definitions:**
- `fun (x, y) -> body` → `fun x y -> body`
- `let f (x, y) = body` → `let f x y = body`
- `let rec f (x, y, z) = body` → `let rec f x y z = body`

**Type signatures:**
- `'a * 'b -> 'c` → `'a -> 'b -> 'c`
- `'a * 'b * 'c -> 'd` → `'a -> 'b -> 'c -> 'd`

**Call sites:**
- `f (a, b)` → `f a b`
- `func (x, y, z)` → `func x y z`

## When to Use This Skill

Use this skill when:
- Porting SML modules that use tuple parameters (common in original Twelf code)
- Modernizing ported code to follow OCaml idioms
- Refactoring modules to use curried style for better composability

## Automated Workflow

The project provides automation scripts for this task:

### Step 1: Convert Function Definitions

```bash
./curry_convert.sh lib/module/file.ml
```

This converts function definitions in place and creates a `.backup` file. Supports:
- `fun (x, y) ->` patterns
- `let f (x, y) =` patterns
- `let rec f (x, y, z) =` patterns
- 2 and 3 parameter tuples

### Step 2: Fix Call Sites

```bash
./fix_call_sites.sh lib/module/file.ml
# or auto-process all files with backups:
./fix_call_sites.sh --auto
```

This updates call sites to match the curried definitions by:
- Extracting function names changed in the diff
- Converting calls from `func (a, b)` to `func a b`

### Step 3: Update Type Signatures

**Manually update** `.mli` interface files and type annotations:
- Change parameter types from `'a * 'b` to `'a -> 'b`
- Update return type arrows accordingly

### Step 4: Test

```bash
dune build --profile=sane
```

Review compiler errors for:
- Missed call sites (complex expressions, nested patterns)
- Type signature mismatches
- Cases where currying breaks existing patterns

## Examples

### Before (SML-style uncurried):
```ocaml
let rec traverse (tree, depth) =
  match tree with
  | Leaf -> depth
  | Node (l, r) -> max (traverse (l, depth + 1)) (traverse (r, depth + 1))

val traverse : tree * int -> int
```

### After (OCaml-style curried):
```ocaml
let rec traverse tree depth =
  match tree with
  | Leaf -> depth
  | Node (l, r) -> max (traverse l (depth + 1)) (traverse r (depth + 1))

val traverse : tree -> int -> int
```

## Limitations and Edge Cases

The automation scripts handle simple cases but **cannot** convert:

1. **Complex patterns in tuples:**
   ```ocaml
   fun ((x, y), z) -> ...  (* needs manual conversion *)
   ```

2. **Nested function calls with complex expressions:**
   ```ocaml
   f ((g x, h y), z)  (* may need manual fixes *)
   ```

3. **Higher-order functions with tuple parameters:**
   ```ocaml
   List.map (fun (x, y) -> x + y) pairs
   (* The fun itself is converted, but context may need changes *)
   ```

4. **Match patterns with tuples:**
   ```ocaml
   match expr with
   | (x, y) -> ...  (* pattern matching should stay as-is *)
   ```

5. **Intentional tuples as single values:**
   ```ocaml
   (* Sometimes tuples are semantic - don't convert these *)
   type point = int * int
   let origin = (0, 0)  (* keep this *)
   ```

## Manual Review Checklist

After automation:

- [ ] Check all compiler errors in affected modules
- [ ] Review `.mli` files for type signature updates
- [ ] Look for missed call sites (grep for function names)
- [ ] Verify semantics haven't changed (especially for partial application)
- [ ] Test with `dune build --profile=sane`
- [ ] Run relevant tests if available
- [ ] Check for opportunities to use partial application
- [ ] Remove `.backup` files after confirming changes

## Rollback

If needed, restore from backups:
```bash
for f in lib/**/*.backup; do mv "$f" "${f%.backup}"; done
```

## Project Context

This is part of the ongoing SML→OCaml port of the Twelf theorem prover. The original SML code heavily uses uncurried functions, while OCaml idiomatically prefers curried style for better composability and partial application.