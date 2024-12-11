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
