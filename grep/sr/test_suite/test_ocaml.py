import tree_sitter as TS 
import tree_sitter_ocaml

LANGUAGE = TS.Language(tree_sitter_ocaml.language_ocaml())
PARSER = TS.Parser(LANGUAGE)
def test_ocaml_code(code : str) -> bool | str:
    tree = PARSER.parse(bytes(code,"utf-8"))
    query_err = TS.Query(LANGUAGE, "(ERROR)")
    query_cursor_err = TS.QueryCursor(query_err)
    query_miss = TS.Query(LANGUAGE, "(MISSING)")
    query_cursor_miss = TS.QueryCursor(query_miss)
    query_miss_match : list[ _ ] = query_cursor_miss.matches(tree.root_node)
    query_err_match : list[ _ ] = query_cursor_err.matches(tree.root_node)
    if tree == None or query_err_match != [] or query_miss_match != []:
        err_msg = ("Error parsing code:", code) + ("Error matches:", query_err_match) + ("Missing matches:", query_miss_match)
        return err_msg
    else : 
        print ("Code parsed successfully:", code)
        return True
    