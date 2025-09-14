import lark


grammar = """

start : var theory rules
var : "(" "VAR" NAME*  ")"
theory : "(" "THEORY" equations ")"
equations : "(" "EQUATIONS" equation* ")"
equation : term "==" term
term : NAME | NAME "(" term ("," term)* ")"
rules : "(" "RULES" rule* ")"
rule : term "->" term
NAME : /[a-zA-Z0-9_]+/
%import common.WS
%ignore WS
"""


example = """

(VAR X Y Z)
(THEORY
  (EQUATIONS
    m(1,X) == X
    m(X,1) == X
    m(X,i(X)) == 1
    m(i(X),X) == 1
    m(m(X,Y),Z) == m(X,m(Y,Z))
   )
)
(RULES 
    f(x,y) -> x
    f(x,y) -> x
    )

"""

parser = lark.Lark(grammar, start="start", parser="lalr")


def test():
    """
    >>> tree = parser.parse(example)
    """
