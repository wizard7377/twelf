import tree_sitter as TS 
import tree_sitter_ocaml

LANGUAGE = TS.Language(tree_sitter_ocaml.language_ocaml())
PARSER = TS.Parser(LANGUAGE)
def test_ocaml_code(code : str) -> bool:
    tree = PARSER.parse(bytes(code,"utf-8"))
    query_err = TS.Query(LANGUAGE, "(ERROR)")
    query_cursor_err = TS.QueryCursor(query_err)
    query_miss = TS.Query(LANGUAGE, "(MISSING)")
    query_cursor_miss = TS.QueryCursor(query_miss)
    query_miss_match : list[ _ ] = query_cursor_miss.matches(tree.root_node)
    query_err_match : list[ _ ] = query_cursor_err.matches(tree.root_node)
    if tree == None or query_err_match == [] or query_miss_match == []:
        print ("Error parsing code:", code);
        print ("Error matches:", query_err_match)
        print ("Missing matches:", query_miss_match)
        return False
    else : 
        print ("Code parsed successfully:", code)
        return True
    