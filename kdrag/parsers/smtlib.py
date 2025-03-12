import lark

# WIP
grammar = r"""

start: command*

command : "(" "push" ")" -> push
        | "(" "pop" ")" -> pop
        | "(" "assert" term ")" -> assert
        | "(" "check-sat" ")" -> check_sat
        | "(" "get-model" ")" -> get_model
        | "(" "exit" ")" -> exit
       // | "(" "declare-fun" NAME "(" sort_list ")" sort ")" -> declare_fun
       // | "(" "define-fun" NAME "(" sorted_var_list ")" sort term ")" -> define_fun
       // | "(" "declare-sort" NAME NUMERIC ")" -> declare_sort

term : NAME
     | "(" NAME term* ")"
     | "(" "=" term term ")" -> eq
     | NUMBER

NAME : /[a-zA-Z][a-zA-Z0-9_]*/
NUMBER : /\d+/

%import common.WS
%ignore WS
"""

parser = lark.Lark(grammar, start="start", parser="lalr")


sexp_grammar = r"""

start : list*
_spec_constant : numeral | decimal | hexadecimal | binary | string
_s_expr : _spec_constant | _symbol |  list // keyword
list : "(" _s_expr* ")"
hexadecimal : "#x" ("0".."9" | "a".."f" | "A".."F")+
decimal : NUMERIC+ "." NUMERIC+
binary : "#b" ("0" | "1")+
simple_symbol : NONNUMCHAR CHARS*
_symbol : simple_symbol | hexadecimal | binary
keyword : ":" simple_symbol
numeral : NUMERIC+
// /([a-zA-Z]|[\+\-=/\\*\%\?\!\.\$])+/  // 
NONNUMCHAR : "a".."z" | "A".."Z" | "+" | "-" | "/" | "*" | "=" | "%" | "?" | "!" | "." | "$" | "_" | "~" | "&" | "^" | "<" | ">" | "@"
CHARS : NUMERIC | NONNUMCHAR
NUMERIC              : "0".."9"
LOWER_ALPHA          : "a".."z"
UPPER_ALPHA          : "A".."Z"
string : STRING
%import common.ESCAPED_STRING   -> STRING
%import common.WS
%ignore WS
"""

parser = lark.Lark(sexp_grammar, start="start")


def test():
    parser.parse("(assert (= x 1))")
