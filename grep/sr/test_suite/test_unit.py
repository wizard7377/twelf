"""Focused unit tests for SML to OCaml conversion."""

import re
import sys
import unittest
from pathlib import Path

import tree_sitter as TS

# Setup path for imports
ROOT_DIR = Path(__file__).resolve().parents[1]
PY_BINDINGS = ROOT_DIR / "python"
SRC_DIR = ROOT_DIR / "src"
if str(PY_BINDINGS) not in sys.path:
	sys.path.append(str(PY_BINDINGS))
if str(SRC_DIR) not in sys.path:
	sys.path.append(str(SRC_DIR))

from test_ocaml import test_ocaml_code
from sml_process import (
	PARSER as SML_PARSER,
	OCAML_RESERVED_RENAMES,
	SML_TO_OCAML_NAMES,
	process_code,
	process_name_lower,
)

KEYWORDS = {
	"val",
	"fun",
	"datatype",
	"type",
	"exception",
	"handle",
	"fn",
	"case",
	"of",
	"let",
	"in",
	"end",
	"if",
	"then",
	"else",
	"while",
	"do",
	"done",
	"for",
	"to",
	"downto",
	"raise",
	"and",
	"local",
	"open",
	"struct",
	"sig",
	"functor",
	"with",
	"match",
	"try",
	"module",
	"rec",
	"andalso",
	"orelse",
	"op",
	"as",
	"ref",
}

IDENTIFIER_RE = re.compile(r"^'+[A-Za-z_][A-Za-z0-9_']*$|^[A-Za-z_][A-Za-z0-9_']*$|^\d+$")


def _has_errors(tree: TS.Tree) -> bool:
	stack = [tree.root_node]
	while stack:
		node = stack.pop()
		if node.type == "ERROR" or getattr(node, "is_missing", False):
			return True
		stack.extend(node.children)
	return False


def _should_keep(snippet: str) -> bool:
	text = snippet.strip()
	if not text or text.lower() in KEYWORDS:
		return False
	return bool(IDENTIFIER_RE.match(text))


def _collect_tokens(tree: TS.Tree, code_bytes: bytes) -> set[str]:
	tokens: set[str] = set()
	stack = [tree.root_node]
	while stack:
		node = stack.pop()
		if node.child_count == 0:
			snippet = code_bytes[node.start_byte : node.end_byte].decode("utf-8", errors="ignore")
			if _should_keep(snippet):
				tokens.add(snippet)
		else:
			stack.extend(node.children)
	return tokens


def _normalize_sml_token(token: str) -> str:
	mapped = SML_TO_OCAML_NAMES.get(token, token)
	mapped = OCAML_RESERVED_RENAMES.get(mapped, mapped)
	if mapped.startswith("'"):
		return mapped
	if mapped and mapped[0].isupper():
		return mapped
	return process_name_lower(mapped)


def _normalized_tokens(tree: TS.Tree, code_bytes: bytes, is_sml: bool) -> set[str]:
	raw_tokens = _collect_tokens(tree, code_bytes)
	if not is_sml:
		return raw_tokens
	return {_normalize_sml_token(token) for token in raw_tokens}


class TestFocusedConversions(unittest.TestCase):
	"""Small, targeted tests for individual SML constructs."""

	def _assert_conversion_equivalent(self, sml_source: str, expected_snippets: tuple[str, ...] = ()) -> str:
		sml_tree = SML_PARSER.parse(sml_source.encode("utf-8"))
		self.assertFalse(_has_errors(sml_tree), "SML input failed to parse cleanly")

		ocaml_code = process_code(sml_source)
		parse_result = test_ocaml_code(ocaml_code)
		self.assertIsInstance(parse_result, TS.Tree, f"OCaml parse failed: {parse_result}")

		ocaml_tree: TS.Tree = parse_result  # type: ignore[assignment]
		self.assertFalse(_has_errors(ocaml_tree), "OCaml output contained parse errors")

		sml_tokens = _normalized_tokens(sml_tree, sml_source.encode("utf-8"), is_sml=True)
		ocaml_tokens = _normalized_tokens(ocaml_tree, ocaml_code.encode("utf-8"), is_sml=False)
		missing = sml_tokens - ocaml_tokens
		self.assertTrue(
			not missing,
			f"Converted OCaml code is missing identifiers: {missing}\nOCaml output:\n{ocaml_code}",
		)

		for snippet in expected_snippets:
			self.assertIn(snippet, ocaml_code)

		return ocaml_code

	def test_feature_snippets(self):
		cases = [
			(
				"list types and expressions",
				"val xs : int list = [1, 2, 3]",
				("[", ";", "xs"),
			),
			(
				"tuple type and expressions",
				'val pair : int * string = (1, "one")',
				("*", "pair"),
			),
			(
				"type declaration and usages",
				"type point = int * int\nval origin : point = (0, 0)",
				("type", "point", "origin"),
			),
			(
				"constructor declarations and usages",
				"datatype color = Red | Blue of int\nval sample = Blue 3",
				("Red", "Blue"),
			),
			(
				"top level and expression level bindings",
				"val base = 10\nval extended = let val y = 5 in base + y end",
				("let", "base", "extended"),
			),
			(
				"exceptions",
				'exception Boom of string\nval _ = raise (Boom "oops")',
				("exception", "Boom", "raise"),
			),
			(
				"references",
				"val counter = ref 0\nval _ = counter := !counter + 1",
				(":=", "counter"),
			),
			(
				"function and value definitions with multiple clauses",
				"fun fact 0 = 1 | fact n = n * fact (n - 1)",
				("fact", "rec"),
			),
			(
				"if then statements",
				"fun sign n = if n > 0 then 1 else ~1",
				("if", "then", "else"),
			),
			(
				"while loop",
				"val r = ref 0\nval _ = while !r < 2 do r := !r + 1",
				("while", "done"),
			),
			(
				"for loop",
				"val total = let val acc = ref 0 in for i = 0 to 3 do acc := !acc + i; !acc end",
				("for", "to"),
			),
			(
				"sequencing",
				'val seq = (print "a"; print "b"; 3)',
				(";", "seq"),
			),
			(
				"recursion and pattern matching",
				"fun head xs = case xs of [] => NONE | x :: _ => SOME x",
				("match", "Some"),
			),
			(
				"record types and expressions",
				'type person = {name:string, age:int}\nval p = {name="Bob", age=30}',
				("{", "name", "age"),
			),
			(
				"function type and lambdas",
				"val incr : int -> int = fn x => x + 1",
				("fun", "->"),
			),
		]

		for name, sml_source, snippets in cases:
			with self.subTest(name=name):
				self._assert_conversion_equivalent(sml_source, expected_snippets=snippets)


if __name__ == "__main__":
	unittest.main()
