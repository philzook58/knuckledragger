import lark

# https://github.com/inpefess/tptp-lark-parser/blob/master/tptp_lark_parser/resources/TPTP.lark
# https://github.com/TPTPWorld/SyntaxBNF/blob/master/SyntaxBNF-v9.0.0.8
fof_grammar = r"""
start                : fof*
cnf       : "cnf" "(" NAME "," FORMULA_ROLE "," cnf_formula ")"  "."
fof       : "fof" "(" NAME "," FORMULA_ROLE "," fof_formula ")"  "." 

FORMULA_ROLE         :  "axiom" | "conjecture"

?fof_formula         :  fof_unit_formula "<=>" fof_unit_formula -> iff
                     | fof_unit_formula "=>" fof_unit_formula -> implies
                     | fof_unit_formula "<=" fof_unit_formula -> reverse_implies
                     | fof_or_formula
?fof_or_formula       : fof_and_formula  ("|" fof_and_formula)*
?fof_and_formula      : fof_unit_formula ("&" fof_unit_formula)*
?fof_unit_formula     : "~" fof_unit_formula -> not_formula 
                      | term "!=" term      -> diseq
                      | term "=" term  ->      eq
                      | "(" fof_formula ")" 
                      | term  -> predicate
                      | "!" "[" fof_variable_list "]" ":" fof_unit_formula -> forall
                      | "?" "[" fof_variable_list "]" ":" fof_unit_formula -> exists

                      
?cnf_formula          : disjunction | "(" disjunction ")"
disjunction         : literal ("|" cnf_formula)*
literal              : atomic_formula -> poslit 
                    | "~" atomic_formula -> neglit
                    | term "!=" term  -> diseq
                    | term "=" term -> eq


arguments            : term ("," term)*

term                :  NAME -> const
            |        | variable -> var
                     |  NAME "(" arguments ")" -> fun_app


FOF_QUANTIFIER       : "!" | "?"
fof_variable_list    : variable ("," variable)*

variable : UPPER_WORD

NONASSOC_CONNECTIVE  : "<=>" | "=>" | "<="  // | "<~>" | "~|" | "~&"

NAME                 : LOWER_WORD
UPPER_WORD           : UPPER_ALPHA ALPHA_NUMERIC*
LOWER_WORD           : LOWER_ALPHA ALPHA_NUMERIC*
NUMERIC              : "0".."9"
LOWER_ALPHA          : "a".."z"
UPPER_ALPHA          : "A".."Z"
ALPHA_NUMERIC        : (LOWER_ALPHA | UPPER_ALPHA | NUMERIC | "_") 

%import common.WS
%ignore WS

"""


term_grammar = r"""
term                :  NAME -> const
            |        | _variable -> var
                     | NAME "(" term ("," term)* ")" -> fun_app


FOF_QUANTIFIER       : "!" | "?"
fof_variable_list    : _variable ("," _variable)*

_variable : UPPER_WORD

NONASSOC_CONNECTIVE  : "<=>" | "=>" | "<="  // | "<~>" | "~|" | "~&"

NAME                 : LOWER_WORD
UPPER_WORD          : UPPER_ALPHA ALPHA_NUMERIC*
LOWER_WORD           : LOWER_ALPHA ALPHA_NUMERIC*
NUMERIC              : "0".."9"
LOWER_ALPHA          : "a".."z"
UPPER_ALPHA          : "A".."Z"
ALPHA_NUMERIC        : (LOWER_ALPHA | UPPER_ALPHA | NUMERIC | "_") 

%import common.WS
%ignore WS
"""

term_parser = lark.Lark(term_grammar, start="term", parser="lalr")


def test():
    """
    >>> term_parser.parse("f(Xy1,g(y23))")
    Tree('fun_app', [Token('NAME', 'f'), Tree('var', [Token('UPPER_WORD', 'Xy1')]), Tree('fun_app', [Token('NAME', 'g'), Tree('const', [Token('NAME', 'y23')])])])

    """
