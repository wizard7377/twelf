import tree_sitter as TS 
import tree_sitter_ocaml

LANGUAGE = TS.Language(tree_sitter_ocaml.language_ocaml())
PARSER = TS.Parser(LANGUAGE)
def test_ocaml_code(code: str) -> TS.Tree | list[tuple[TS.Node, str]]:
    tree = PARSER.parse(bytes(code, "utf-8"))
    problem_nodes: list[tuple[TS.Node, str]] = []

    if tree is not None:
        stack = [tree.root_node]
        while stack:
            node = stack.pop()
            if node.type == "ERROR" or node.is_missing:
                snippet = code[node.start_byte:node.end_byte]
                problem_nodes.append((node, snippet))
            stack.extend(node.children)

    if tree is None or problem_nodes:
        for node, snippet in problem_nodes:
            # Print a small description so callers can see what failed, including the text span.
            start = node.start_point
            end = node.end_point
            #print(f"Problem node {node.type} {start}->{end}: '{snippet}'")
        return problem_nodes

    #print("Code parsed successfully")
    return tree
    