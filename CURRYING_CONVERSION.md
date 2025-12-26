# Currying Conversion Strategy

## Overview
Converting the Twelf OCaml port from uncurried (SML-style) to curried (OCaml-idiomatic) function style.

## Conversion Patterns

### Pattern 1: Anonymous Functions with Tuples
**Before:**
```ocaml
List.foldr (fun (a, s) -> " " ^ cidToString a ^ s) ".\n" cids
```

**After:**
```ocaml
List.foldr (fun a s -> " " ^ cidToString a ^ s) ".\n" cids
```

### Pattern 2: Function Definitions with Tuple Parameters
**Before:**
```ocaml
let name (x, y) = x + y
```

**After:**
```ocaml
let name x y = x + y
```

### Pattern 3: Pattern Matching Functions
**Before:**
```ocaml
let rec ratio = function
  | (0, 0) -> 1.0
  | (c, 0) -> 1.1
  | (c, m) -> (Real.fromInt c) / (Real.fromInt m)
```

**After:**
```ocaml
let rec ratio c m = match c, m with
  | 0, 0 -> 1.0
  | c, 0 -> 1.1
  | c, m -> (Real.fromInt c) / (Real.fromInt m)
```

### Pattern 4: Nested Tuples
**Before:**
```ocaml
fun (nv, (l', E)) -> (* body *)
```

**After:**
```ocaml
fun nv (l', E) -> (* body *)
(* Or fully curry if nested tuple should also be separated *)
fun nv l' E -> (* body *)
```

### Pattern 5: Function Type Signatures
**Before:**
```ocaml
val name : (int * string) -> result
```

**After:**
```ocaml
val name : int -> string -> result
```

## Conversion Order

1. **Basis Library** - Update helper functions to be curried
2. **Small Modules** - Heuristic (6 instances) - proof of concept
3. **Core Modules** - Lambda (6), Cover (15), Compile (14)
4. **Large Modules** - Meta (47), Opsem (46), Solvers (43), Frontend (43)
5. **Remaining** - M2, Terminate, Style, Prover, etc.

## Important Considerations

1. **Higher-order functions**: When passing curried functions to higher-order functions, call sites may need updating
2. **Partial application**: Curried functions enable partial application - may simplify some code
3. **Type signatures**: .mli files must be updated to match
4. **Testing**: Build and test after each module conversion
5. **Breaking changes**: Function signature changes are breaking - must update all call sites

## Progress Tracking

- [x] Analysis complete - 58 files identified
- [ ] Basis library
- [ ] Heuristic module (proof of concept)
- [ ] Lambda module
- [ ] Cover module
- [ ] Compile module
- [ ] Meta module
- [ ] Opsem module
- [ ] Solvers module
- [ ] Frontend module
- [ ] Remaining modules
- [ ] Full test suite passing
