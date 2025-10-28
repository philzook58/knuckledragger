r"""
Lean-flavored logic parser for knuckledragger.

Supports:
- forall (x : T), body
- exists (x : T), body
- -> (implies)
- /\ (and)
- \/ (or)
- Predicates and constants
- { python expr } for interpolation

Example:
    >>> from kdrag.parsers.logic import parse
    >>> import kdrag.smt as smt
    >>> x = smt.Int('x')
    >>> expr = parse("forall (y : Int), y + 0 == y", {'Int': smt.IntSort()})
    >>> print(expr)
    ForAll(y, y + 0 == y)
"""

import re
from typing import Any
import kdrag.smt as smt


# Token patterns (order matters for matching)
tokens = [
    ("WS", r"\s+"),
    ("COMMENT", r"--[^\n]*"),
    ("FORALL", r"\bforall\b"),
    ("EXISTS", r"\bexists\b"),
    ("IMPLIES", r"->"),
    ("AND", r"/\\"),
    ("OR", r"\\/"),
    ("NOT", r"~|¬|\bnot\b"),
    ("LPAREN", r"\("),
    ("RPAREN", r"\)"),
    ("LBRACE", r"\{"),
    ("RBRACE", r"\}"),
    ("COMMA", r","),
    ("COLON", r":"),
    ("LE", r"<="),
    ("GE", r">="),
    ("LT", r"<"),
    ("GT", r">"),
    ("EQ", r"=="),
    ("NE", r"!="),
    ("PLUS", r"\+"),
    ("MINUS", r"-"),
    ("TIMES", r"\*"),
    ("DIV", r"/"),
    ("NUMBER", r"-?\d+(?:\.\d+)?"),
    ("TRUE", r"\bTrue\b"),
    ("FALSE", r"\bFalse\b"),
    ("IDENT", r"[A-Za-z_][A-Za-z0-9_]*"),
]

regex = "|".join(f"(?P<{name}>{pattern})" for name, pattern in tokens)
pattern = re.compile(regex)


class ParseError(Exception):
    """Raised when parsing fails."""
    pass


class Parser:
    """
    Recursive descent parser for Lean-flavored logic expressions.
    """
    
    def __init__(self, text: str, env: dict[str, Any] | None = None):
        """
        Initialize parser.
        
        Args:
            text: The text to parse
            env: Environment mapping names to sorts and values
        """
        self.text = text
        self.env = env or {}
        self.tokens = list(self._tokenize())
        self.pos = 0
    
    def _tokenize(self):
        """Tokenize the input text."""
        curr = 0
        for match in pattern.finditer(self.text):
            if match.start() != curr:
                raise ParseError(
                    f"Unexpected characters at position {curr}: "
                    f"{self.text[curr:match.start()]!r}"
                )
            curr = match.end()
            if match.lastgroup not in ("WS", "COMMENT"):
                yield (match.lastgroup, match.group(), match.start())
        
        if curr != len(self.text):
            raise ParseError(
                f"Unexpected characters at end: {self.text[curr:]!r}"
            )
    
    def peek(self):
        """Peek at current token without consuming."""
        if self.pos < len(self.tokens):
            return self.tokens[self.pos]
        return None
    
    def consume(self, expected: str | None = None):
        """Consume and return current token."""
        if self.pos >= len(self.tokens):
            if expected:
                raise ParseError(f"Expected {expected} but reached end of input")
            return None
        
        token = self.tokens[self.pos]
        if expected and token[0] != expected:
            raise ParseError(
                f"Expected {expected} but got {token[0]} at position {token[2]}"
            )
        self.pos += 1
        return token
    
    def parse(self):
        """Parse the entire expression."""
        expr = self.parse_implies()
        if self.peek() is not None:
            raise ParseError(f"Unexpected token after expression: {self.peek()}")
        return expr
    
    def parse_implies(self):
        """Parse implication (lowest precedence)."""
        left = self.parse_or()
        
        token = self.peek()
        if token and token[0] == "IMPLIES":
            self.consume("IMPLIES")
            right = self.parse_implies()
            return smt.Implies(left, right)
        
        return left
    
    def parse_or(self):
        """Parse disjunction."""
        left = self.parse_and()
        
        token = self.peek()
        while token and token[0] == "OR":
            self.consume("OR")
            right = self.parse_and()
            left = smt.Or(left, right)
            token = self.peek()
        
        return left
    
    def parse_and(self):
        """Parse conjunction."""
        left = self.parse_not()
        
        token = self.peek()
        while token and token[0] == "AND":
            self.consume("AND")
            right = self.parse_not()
            left = smt.And(left, right)
            token = self.peek()
        
        return left
    
    def parse_not(self):
        """Parse negation."""
        token = self.peek()
        if token and token[0] == "NOT":
            self.consume("NOT")
            return smt.Not(self.parse_not())
        
        return self.parse_comparison()
    
    def parse_comparison(self):
        """Parse comparison operators."""
        left = self.parse_additive()
        
        token = self.peek()
        if token and token[0] in ("EQ", "NE", "LT", "LE", "GT", "GE"):
            op_token = self.consume()
            assert op_token is not None
            op = op_token[0]
            right = self.parse_additive()
            
            if op == "EQ":
                return left == right
            elif op == "NE":
                return left != right
            elif op == "LT":
                return left < right
            elif op == "LE":
                return left <= right
            elif op == "GT":
                return left > right
            elif op == "GE":
                return left >= right
        
        return left
    
    def parse_additive(self):
        """Parse addition and subtraction."""
        left = self.parse_multiplicative()
        
        token = self.peek()
        while token and token[0] in ("PLUS", "MINUS"):
            op_token = self.consume()
            assert op_token is not None
            op = op_token[0]
            right = self.parse_multiplicative()
            if op == "PLUS":
                left = left + right
            else:
                left = left - right
            token = self.peek()
        
        return left
    
    def parse_multiplicative(self):
        """Parse multiplication and division."""
        left = self.parse_unary()
        
        token = self.peek()
        while token and token[0] in ("TIMES", "DIV"):
            op_token = self.consume()
            assert op_token is not None
            op = op_token[0]
            right = self.parse_unary()
            if op == "TIMES":
                left = left * right
            else:
                left = left / right
            token = self.peek()
        
        return left
    
    def parse_unary(self):
        """Parse unary minus."""
        token = self.peek()
        if token and token[0] == "MINUS":
            self.consume("MINUS")
            return -self.parse_unary()
        
        return self.parse_quantifier()
    
    def parse_quantifier(self):
        """Parse forall/exists quantifiers."""
        token = self.peek()
        if token and token[0] in ("FORALL", "EXISTS"):
            quant_token = self.consume()
            assert quant_token is not None
            quant_type = quant_token[0]
            self.consume("LPAREN")
            
            # Parse variable bindings
            vars = []
            while True:
                name_token = self.consume("IDENT")
                assert name_token is not None
                var_name = name_token[1]
                
                self.consume("COLON")
                sort_token = self.consume("IDENT")
                assert sort_token is not None
                sort_name = sort_token[1]
                
                if sort_name not in self.env:
                    raise ParseError(
                        f"Unknown sort '{sort_name}' at position {sort_token[2]}"
                    )
                
                sort = self.env[sort_name]
                var = smt.Const(var_name, sort)
                vars.append(var)
                
                token = self.peek()
                if token and token[0] == "COMMA":
                    self.consume("COMMA")
                else:
                    break
            
            self.consume("RPAREN")
            self.consume("COMMA")
            
            # Parse body with vars in scope
            old_env = self.env.copy()
            for var in vars:
                self.env[str(var)] = var
            
            body = self.parse_implies()
            self.env = old_env
            
            if quant_type == "FORALL":
                return smt.ForAll(vars, body)
            else:
                return smt.Exists(vars, body)
        
        return self.parse_primary()
    
    def parse_primary(self):
        """Parse primary expressions (atoms, parens, python exprs)."""
        token = self.peek()
        
        if not token:
            raise ParseError("Unexpected end of input")
        
        # Parenthesized expression
        if token[0] == "LPAREN":
            self.consume("LPAREN")
            expr = self.parse_implies()
            self.consume("RPAREN")
            return expr
        
        # Python expression interpolation
        if token[0] == "LBRACE":
            self.consume("LBRACE")
            # Collect tokens until closing brace
            py_tokens = []
            depth = 1
            while depth > 0:
                t = self.consume()
                if not t:
                    raise ParseError("Unclosed {")
                if t[0] == "LBRACE":
                    depth += 1
                elif t[0] == "RBRACE":
                    depth -= 1
                if depth > 0:
                    py_tokens.append(t[1])
            
            py_expr = " ".join(py_tokens)
            # Evaluate python expression in env
            try:
                result = eval(py_expr, {}, self.env)
                return result
            except Exception as e:
                raise ParseError(f"Failed to evaluate Python expression '{py_expr}': {e}")
        
        # Boolean literals
        if token[0] == "TRUE":
            self.consume("TRUE")
            return smt.BoolVal(True)
        
        if token[0] == "FALSE":
            self.consume("FALSE")
            return smt.BoolVal(False)
        
        # Numbers
        if token[0] == "NUMBER":
            num_token = self.consume("NUMBER")
            assert num_token is not None
            num_str = num_token[1]
            if "." in num_str:
                return smt.RealVal(num_str)
            else:
                return smt.IntVal(int(num_str))
        
        # Identifier (variable, constant, or function call)
        if token[0] == "IDENT":
            ident_token = self.consume("IDENT")
            assert ident_token is not None
            name = ident_token[1]
            
            # Check if it's a function call
            next_token = self.peek()
            if next_token and next_token[0] == "LPAREN":
                self.consume("LPAREN")
                args = []
                
                peek_token = self.peek()
                if peek_token and peek_token[0] != "RPAREN":
                    args.append(self.parse_implies())
                    
                    peek_token = self.peek()
                    while peek_token and peek_token[0] == "COMMA":
                        self.consume("COMMA")
                        args.append(self.parse_implies())
                        peek_token = self.peek()
                
                self.consume("RPAREN")
                
                # Look up function in env
                if name in self.env:
                    func = self.env[name]
                    return func(*args)
                else:
                    raise ParseError(f"Unknown function '{name}'")
            
            # It's a variable or constant
            if name in self.env:
                return self.env[name]
            else:
                raise ParseError(f"Unknown identifier '{name}'")
        
        raise ParseError(f"Unexpected token: {token}")


def parse(text: str, env: dict[str, Any] | None = None):
    """
    Parse a Lean-flavored logic expression.
    
    Args:
        text: The expression to parse
        env: Environment mapping names to sorts and values
    
    Returns:
        A Z3 expression representing the parsed formula
    
    Examples:
        >>> import kdrag.smt as smt
        >>> x = smt.Int('x')
        >>> env = {
        ...     'Int': smt.IntSort(),
        ...     'Bool': smt.BoolSort(),
        ...     'x': x
        ... }
        >>> parse("forall (y : Int), y >= 0 -> y + 1 > 0", env)
        ForAll([y], Implies(y >= 0, y + 1 > 0))
        >>> parse("x + 1 == 2", env)
        x + 1 == 2
        >>> parse("True /\\ False", env)
        And(True, False)
    """
    parser = Parser(text, env)
    return parser.parse()
