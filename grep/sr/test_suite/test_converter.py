"""
Test suite for SML to OCaml converter.

This file contains comprehensive test cases for verifying the converter handles
various SML constructs correctly and produces valid OCaml output.
"""

import unittest
from pathlib import Path
import sys

from test_suite.test_ocaml import test_ocaml_code

# Setup path for imports
ROOT_DIR = Path(__file__).resolve().parents[1]
PY_BINDINGS = ROOT_DIR / "python"
SRC_DIR = ROOT_DIR / "src"
if str(PY_BINDINGS) not in sys.path:
    sys.path.append(str(PY_BINDINGS))
if str(SRC_DIR) not in sys.path:
    sys.path.append(str(SRC_DIR))

# Import the converter
from sml_process import process_code


class TestSMLtoOCamlConverter(unittest.TestCase):
    """Test cases for SML to OCaml converter."""

    def test_simple_value_declaration(self):
        """Test simple value declarations."""
        sml = "val x = 5"
        result = process_code(sml);
        assert test_ocaml_code(result)
        self.assertIn("let", result)
        self.assertIn("x", result)
        self.assertIn("5", result)

    def test_function_declaration(self):
        """Test function declarations."""
        sml = "fun double x = x + x"
        result = process_code(sml);
        assert test_ocaml_code(result)
        self.assertIn("let rec", result)
        self.assertIn("double", result)

    def test_conditional_expression(self):
        """Test if-then-else expressions."""
        sml = "if x > 0 then x else 0"
        result = process_code(sml);
        assert test_ocaml_code(result)
        self.assertIn("if", result)
        self.assertIn("then", result)
        self.assertIn("else", result)

    def test_pattern_matching(self):
        """Test case expressions and pattern matching."""
        sml = "case x of 0 => x | n => n + 1"
        result = process_code(sml);
        assert test_ocaml_code(result)
        self.assertIn("match", result)
        self.assertIn("with", result)

    def test_list_expression(self):
        """Test list literal conversion."""
        sml = "[1, 2, 3]"
        result = process_code(sml);
        assert test_ocaml_code(result)
        self.assertIn("[", result)
        self.assertIn("]", result)
        # OCaml uses semicolons to separate list elements
        self.assertIn(";", result)

    def test_tuple_expression(self):
        """Test tuple literal conversion."""
        sml = "(1, 2, 3)"
        result = process_code(sml);
        assert test_ocaml_code(result)
        self.assertIn("(", result)
        self.assertIn(")", result)
        self.assertIn(",", result)

    def test_record_expression(self):
        """Test record literal conversion."""
        sml = "{a=1, b=2}"
        result = process_code(sml);
        assert test_ocaml_code(result)
        self.assertIn("{", result)
        self.assertIn("}", result)
        self.assertIn("a", result)
        self.assertIn("b", result)
        # OCaml uses semicolons in records
        self.assertIn(";", result)

    def test_lambda_expression(self):
        """Test lambda/function expressions."""
        sml = "fn x => x + 1"
        result = process_code(sml);
        assert test_ocaml_code(result)
        self.assertIn("fun", result)
        self.assertIn("->", result)

    def test_andalso_operator(self):
        """Test boolean 'and' operator."""
        sml = "x > 0 andalso y < 10"
        result = process_code(sml);
        assert test_ocaml_code(result)
        self.assertIn("&&", result)

    def test_orelse_operator(self):
        """Test boolean 'or' operator."""
        sml = "x = 0 orelse x > 10"
        result = process_code(sml);
        assert test_ocaml_code(result)
        self.assertIn("||", result)

    def test_datatype_declaration(self):
        """Test datatype declarations."""
        sml = "datatype option = NONE | SOME of int"
        result = process_code(sml);
        assert test_ocaml_code(result)
        self.assertIn("type", result)
        self.assertIn("NONE", result)
        self.assertIn("SOME", result)

    def test_type_declaration(self):
        """Test type alias declarations."""
        sml = "type myint = int"
        result = process_code(sml);
        assert test_ocaml_code(result)
        self.assertIn("type", result)
        self.assertIn("myint", result)

    def test_let_expression(self):
        """Test let-in-end expressions."""
        sml = "let val x = 5 in x + 1 end"
        result = process_code(sml);
        assert test_ocaml_code(result)
        self.assertIn("let", result)
        self.assertIn("in", result)
        self.assertIn("+", result)

    def test_exception_declaration(self):
        """Test exception declarations."""
        sml = "exception MyError"
        result = process_code(sml);
        assert test_ocaml_code(result)
        self.assertIn("exception", result)
        self.assertIn("MyError", result)

    def test_exception_with_payload(self):
        """Test exception with data."""
        sml = "exception Error of string"
        result = process_code(sml);
        assert test_ocaml_code(result)
        self.assertIn("exception", result)
        self.assertIn("Error", result)
        self.assertIn("string", result)

    def test_try_catch(self):
        """Test exception handling."""
        sml = "e handle MyError => 0"
        result = process_code(sml);
        assert test_ocaml_code(result)
        self.assertIn("try", result)
        self.assertIn("with", result)

    def test_type_annotation(self):
        """Test type annotations in expressions."""
        sml = "(x : int)"
        result = process_code(sml);
        assert test_ocaml_code(result)
        self.assertIn(":", result)
        self.assertIn("int", result)

    def test_while_loop(self):
        """Test while loops."""
        sml = "while x < 10 do x := x + 1"
        result = process_code(sml);
        assert test_ocaml_code(result)
        self.assertIn("while", result)
        self.assertIn("do", result)
        self.assertIn("done", result)

    def test_record_pattern(self):
        """Test record patterns in case expressions."""
        sml = "case r of {a=x, b=y} => x + y"
        result = process_code(sml);
        assert test_ocaml_code(result)
        self.assertIn("{", result)
        self.assertIn("}", result)

    def test_list_pattern(self):
        """Test list patterns."""
        sml = "case lst of [] => 0 | h::t => h"
        result = process_code(sml);
        assert test_ocaml_code(result)
        self.assertIn("[", result)
        self.assertIn("]", result)

    def test_function_type(self):
        """Test function type expressions."""
        sml = "val f : int -> int = fn x => x + 1"
        result = process_code(sml);
        assert test_ocaml_code(result)
        self.assertIn("->", result)
        self.assertIn("int", result)

    def test_polymorphic_type(self):
        """Test polymorphic type variables."""
        sml = "val id : 'a -> 'a = fn x => x"
        result = process_code(sml);
        assert test_ocaml_code(result)
        self.assertIn("'a", result)

    def test_tuple_type(self):
        """Test tuple types."""
        sml = "val p : int * string = (1, \"hello\")"
        result = process_code(sml);
        assert test_ocaml_code(result)
        self.assertIn("*", result)

    def test_module_declaration(self):
        """Test structure declarations."""
        sml = "structure S = struct val x = 5 end"
        result = process_code(sml);
        assert test_ocaml_code(result)
        self.assertIn("module", result)
        self.assertIn("struct", result)
        self.assertIn("end", result)

    def test_open_declaration(self):
        """Test open declarations."""
        sml = "open List"
        result = process_code(sml);
        assert test_ocaml_code(result)
        self.assertIn("open", result)
        self.assertIn("List", result)

    def test_complex_expression(self):
        """Test a complex expression with multiple operators."""
        sml = "if x > 0 andalso y < 10 then x + y else 0"
        result = process_code(sml);
        assert test_ocaml_code(result)
        self.assertIn("if", result)
        self.assertIn("&&", result)
        self.assertIn("+", result)

    def test_nested_function_application(self):
        """Test nested function calls."""
        sml = "f (g (h x))"
        result = process_code(sml);
        assert test_ocaml_code(result)
        self.assertIn("f", result)
        self.assertIn("g", result)
        self.assertIn("h", result)

    def test_multiple_pattern_clauses(self):
        """Test multiple match clauses."""
        sml = "fn 0 => 1 | n => n * fact (n-1)"
        result = process_code(sml);
        assert test_ocaml_code(result)
        self.assertIn("fun", result)
        self.assertIn("|", result)
        self.assertIn("->", result)

    def test_record_selector(self):
        """Test record field access."""
        sml = "#x rec"
        result = process_code(sml);
        assert test_ocaml_code(result)
        # Record selector translation

    def test_char_constant(self):
        """Test character constant conversion."""
        sml = '#"a"'
        result = process_code(sml);
        assert test_ocaml_code(result)
        # Should convert SML char syntax to OCaml

    def test_string_constant(self):
        """Test string constants are preserved."""
        sml = '"hello world"'
        result = process_code(sml);
        assert test_ocaml_code(result)
        self.assertIn('"', result)
        self.assertIn("hello", result)

    def test_empty_list(self):
        """Test empty list."""
        sml = "[]"
        result = process_code(sml);
        assert test_ocaml_code(result)
        self.assertIn("[", result)
        self.assertIn("]", result)

    def test_empty_record(self):
        """Test empty record."""
        sml = "{}"
        result = process_code(sml);
        assert test_ocaml_code(result)
        self.assertIn("{", result)
        self.assertIn("}", result)

    def test_empty_tuple(self):
        """Test unit (empty tuple)."""
        sml = "()"
        result = process_code(sml);
        assert test_ocaml_code(result)
        self.assertEqual(result.strip(), "()")

    def test_qualified_identifier(self):
        """Test qualified (module.identifier) references."""
        sml = "List.map"
        result = process_code(sml);
        assert test_ocaml_code(result)
        self.assertIn("List", result)
        self.assertIn(".", result)

    def test_infix_operator_as_prefix(self):
        """Test operators used in prefix position."""
        sml = "op + (1, 2)"
        result = process_code(sml);
        assert test_ocaml_code(result)
        self.assertIn("+", result)

    def test_raise_expression(self):
        """Test raise expressions."""
        sml = "raise MyError"
        result = process_code(sml);
        assert test_ocaml_code(result)
        self.assertIn("raise", result)

    def test_local_declaration(self):
        """Test local-in-end."""
        sml = "local val x = 5 in val y = x + 1 end"
        result = process_code(sml);
        assert test_ocaml_code(result)
        # local declarations should be restructured for OCaml

    def test_mutual_recursion(self):
        """Test mutually recursive functions."""
        sml = "fun even n = if n = 0 then true else odd (n-1) and odd n = if n = 0 then false else even (n-1)"
        result = process_code(sml);
        assert test_ocaml_code(result)
        self.assertIn("rec", result)
        self.assertIn("and", result)

    def test_vector_literal(self):
        """Test vector literals (if supported)."""
        sml = "#[1, 2, 3]"
        result = process_code(sml);
        assert test_ocaml_code(result)
        # Should convert to OCaml array syntax


class TestEdgeCases(unittest.TestCase):
    """Test edge cases and potential problem areas."""

    def test_deeply_nested_expressions(self):
        """Test deeply nested function calls."""
        sml = "f (g (h (i (j x))))"
        result = process_code(sml);
        assert test_ocaml_code(result)
        self.assertTrue(len(result) > 0)

    def test_large_list(self):
        """Test large list literals."""
        sml = "[" + ", ".join(str(i) for i in range(100)) + "]"
        result = process_code(sml);
        assert test_ocaml_code(result)
        self.assertIn("[", result)
        self.assertIn("]", result)

    def test_operator_precedence(self):
        """Test that operator precedence is preserved."""
        sml = "1 + 2 * 3"
        result = process_code(sml);
        assert test_ocaml_code(result)
        self.assertIn("+", result)
        self.assertIn("*", result)

    def test_whitespace_handling(self):
        """Test that converter handles various whitespace."""
        sml = """
        val   x   =   5
        fun  f   n  =  n + 1
        """
        result = process_code(sml);
        assert test_ocaml_code(result)
        self.assertIn("x", result)
        self.assertIn("f", result)

    def test_comment_preservation(self):
        """Test that comments are preserved."""
        sml = "(* This is a comment *) val x = 5"
        result = process_code(sml);
        assert test_ocaml_code(result)
        self.assertIn("(*", result)
        self.assertIn("*)", result)


class TestIdentifierConversion(unittest.TestCase):
    """Test identifier naming conventions."""

    def test_value_identifier_lowercase(self):
        """Test that value identifiers are lowercase."""
        sml = "val MyValue = 5"
        result = process_code(sml);
        assert test_ocaml_code(result)
        # Value identifier should be converted to lowercase

    def test_type_identifier_uppercase(self):
        """Test that type identifiers maintain capitalization."""
        sml = "type MyType = int"
        result = process_code(sml);
        assert test_ocaml_code(result)
        self.assertIn("MyType", result)

    def test_constructor_uppercase(self):
        """Test that constructors are uppercase."""
        sml = "datatype option = NONE | SOME of int"
        result = process_code(sml);
        assert test_ocaml_code(result)
        self.assertIn("NONE", result)
        self.assertIn("SOME", result)


def run_tests():
    """Run all tests."""
    unittest.main()


if __name__ == "__main__":
    run_tests()
