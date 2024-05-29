import re
from dataclasses import dataclass
from typing import List, Any


@dataclass
class Sexp:
    sexp: List[Any]


# \s* is whitespace follow by digits or symbol or ( or )
token_pattern = re.compile(
    r"\s*(?:(\d+)|([A-Za-z\-!=\+\*\_<>]+[A-Za-z0-9\-!=\+\*\_<>]*)|(\()|(\)))"
)


def tokenize(s):
    for match in token_pattern.finditer(s):
        yield match.groups()


def parse_expression(iterator):
    """Parse an expression from the token iterator."""
    items = []
    for number, symbol, lparen, rparen in iterator:
        if lparen:
            items.append(parse_expression(iterator))
        elif rparen:
            return items
        elif number:
            items.append(int(number))
        elif symbol:
            items.append(symbol)
        else:
            raise SyntaxError("Unexpected token")
    return items


def parse_sexp(s):
    """Parse an S-expression from a string."""
    tokens = tokenize(s)
    try:
        # The outermost list is not required for a valid S-expression,
        # so we extract the single expression inside it.
        result = parse_expression(tokens)
        # Check for trailing tokens
        for _ in tokens:
            raise SyntaxError("Trailing tokens")
        return result
    except StopIteration:
        raise SyntaxError("Unexpected end of input")
