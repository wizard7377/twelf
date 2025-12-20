"""
Example SML programs and their OCaml conversions.

This file demonstrates the converter in action with various SML programs.
"""

from pathlib import Path
import sys

# Setup path for imports
ROOT_DIR = Path(__file__).resolve().parents[1]
PY_BINDINGS = ROOT_DIR / "python"
SRC_DIR = ROOT_DIR / "src"
if str(PY_BINDINGS) not in sys.path:
    sys.path.append(str(PY_BINDINGS))
if str(SRC_DIR) not in sys.path:
    sys.path.append(str(SRC_DIR))

from sml_process import process_code

# Example 1: Factorial function
EXAMPLE_1_SML = """
fun factorial n =
  if n <= 1 then 1
  else n * factorial (n - 1)
"""

print("=" * 60)
print("Example 1: Factorial Function")
print("=" * 60)
print("SML Input:")
print(EXAMPLE_1_SML)
print("\nOCaml Output:")
print(process_code(EXAMPLE_1_SML))
print()

# Example 2: List operations
EXAMPLE_2_SML = """
val numbers = [1, 2, 3, 4, 5]
fun sum lst =
  case lst of
    [] => 0
    | h::t => h + sum t
val total = sum numbers
"""

print("=" * 60)
print("Example 2: List Operations")
print("=" * 60)
print("SML Input:")
print(EXAMPLE_2_SML)
print("\nOCaml Output:")
print(process_code(EXAMPLE_2_SML))
print()

# Example 3: Pattern matching with records
EXAMPLE_3_SML = """
datatype person = Person of {name: string, age: int}
fun is_adult p =
  case p of
    Person {name=_, age=a} => a >= 18
"""

print("=" * 60)
print("Example 3: Datatype with Records")
print("=" * 60)
print("SML Input:")
print(EXAMPLE_3_SML)
print("\nOCaml Output:")
print(process_code(EXAMPLE_3_SML))
print()

# Example 4: Higher-order functions
EXAMPLE_4_SML = """
fun map f lst =
  case lst of
    [] => []
    | h::t => f h :: map f t

fun double x = x * 2
val doubled = map double [1, 2, 3]
"""

print("=" * 60)
print("Example 4: Higher-order Functions")
print("=" * 60)
print("SML Input:")
print(EXAMPLE_4_SML)
print("\nOCaml Output:")
print(process_code(EXAMPLE_4_SML))
print()

# Example 5: Exception handling
EXAMPLE_5_SML = """
exception DivideByZero

fun safe_divide x y =
  if y = 0 then raise DivideByZero
  else x div y

val result = safe_divide 10 2 handle DivideByZero => 0
"""

print("=" * 60)
print("Example 5: Exception Handling")
print("=" * 60)
print("SML Input:")
print(EXAMPLE_5_SML)
print("\nOCaml Output:")
print(process_code(EXAMPLE_5_SML))
print()

# Example 6: Polymorphic functions
EXAMPLE_6_SML = """
fun identity x = x
fun compose f g x = f (g x)
fun apply f x = f x
"""

print("=" * 60)
print("Example 6: Polymorphic Functions")
print("=" * 60)
print("SML Input:")
print(EXAMPLE_6_SML)
print("\nOCaml Output:")
print(process_code(EXAMPLE_6_SML))
print()

# Example 7: Type annotations and signatures
EXAMPLE_7_SML = """
val increment : int -> int = fn x => x + 1
val concat : string * string -> string = fn (s1, s2) => s1 ^ s2
fun id (x : 'a) : 'a = x
"""

print("=" * 60)
print("Example 7: Type Annotations")
print("=" * 60)
print("SML Input:")
print(EXAMPLE_7_SML)
print("\nOCaml Output:")
print(process_code(EXAMPLE_7_SML))
print()

# Example 8: Modules and structures
EXAMPLE_8_SML = """
structure Stack =
struct
  type 'a stack = 'a list
  fun push x s = x :: s
  fun pop s =
    case s of
      [] => raise Empty
      | h::t => (h, t)
end
"""

print("=" * 60)
print("Example 8: Structures")
print("=" * 60)
print("SML Input:")
print(EXAMPLE_8_SML)
print("\nOCaml Output:")
print(process_code(EXAMPLE_8_SML))
print()

# Example 9: Let expressions
EXAMPLE_9_SML = """
val result =
  let
    val x = 5
    val y = 10
    fun add a b = a + b
  in
    add x y
  end
"""

print("=" * 60)
print("Example 9: Let Expressions")
print("=" * 60)
print("SML Input:")
print(EXAMPLE_9_SML)
print("\nOCaml Output:")
print(process_code(EXAMPLE_9_SML))
print()

# Example 10: Mutually recursive functions
EXAMPLE_10_SML = """
fun even n =
  if n = 0 then true
  else odd (n - 1)
and odd n =
  if n = 0 then false
  else even (n - 1)
"""

print("=" * 60)
print("Example 10: Mutually Recursive Functions")
print("=" * 60)
print("SML Input:")
print(EXAMPLE_10_SML)
print("\nOCaml Output:")
print(process_code(EXAMPLE_10_SML))
print()

# Example 11: Tuples and records
EXAMPLE_11_SML = """
val pair = (1, 2)
val record = {name="Alice", age=30, city="NYC"}
fun get_name r = #name r
"""

print("=" * 60)
print("Example 11: Tuples and Records")
print("=" * 60)
print("SML Input:")
print(EXAMPLE_11_SML)
print("\nOCaml Output:")
print(process_code(EXAMPLE_11_SML))
print()

# Example 12: Boolean operations
EXAMPLE_12_SML = """
fun both a b = a andalso b
fun either a b = a orelse b
fun negate a = if a then false else true
"""

print("=" * 60)
print("Example 12: Boolean Operations")
print("=" * 60)
print("SML Input:")
print(EXAMPLE_12_SML)
print("\nOCaml Output:")
print(process_code(EXAMPLE_12_SML))
print()

# Example 13: Lambda expressions
EXAMPLE_13_SML = """
val square = fn x => x * x
val add = fn (x, y) => x + y
val apply = fn f => fn x => f x
"""

print("=" * 60)
print("Example 13: Lambda Expressions")
print("=" * 60)
print("SML Input:")
print(EXAMPLE_13_SML)
print("\nOCaml Output:")
print(process_code(EXAMPLE_13_SML))
print()

# Example 14: Nested case expressions
EXAMPLE_14_SML = """
fun classify pair =
  case pair of
    (0, 0) => "origin"
    | (0, _) => "y-axis"
    | (_, 0) => "x-axis"
    | (x, y) => if x > 0 andalso y > 0 then "quadrant I"
                else if x < 0 andalso y > 0 then "quadrant II"
                else if x < 0 andalso y < 0 then "quadrant III"
                else "quadrant IV"
"""

print("=" * 60)
print("Example 14: Nested Case Expressions")
print("=" * 60)
print("SML Input:")
print(EXAMPLE_14_SML)
print("\nOCaml Output:")
print(process_code(EXAMPLE_14_SML))
print()

# Example 15: Type declarations
EXAMPLE_15_SML = """
type myint = int
type pair = int * int
type name = string
datatype color = Red | Green | Blue
"""

print("=" * 60)
print("Example 15: Type Declarations")
print("=" * 60)
print("SML Input:")
print(EXAMPLE_15_SML)
print("\nOCaml Output:")
print(process_code(EXAMPLE_15_SML))
print()

print("\n" + "=" * 60)
print("Examples completed!")
print("=" * 60)
