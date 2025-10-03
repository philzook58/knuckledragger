import re


type Sexp = str | int | float | list["Sexp"]

tokens = [
    ("WS", r"\s+"),
    ("COMMENT", r";[^\n\r]*"),
    ("LPAREN", r"\("),
    ("RPAREN", r"\)"),
    ("NUMBER", r"-?\d+(?:\.\d+)?"),
    ("IDENT", r"[A-Za-z\-!=\+\*\_\.<>][A-Za-z0-9\-!=\+\*\_\.<>]*"),
    # TODO ("QUOTE", r"\|")
]

regex = "|".join(f"(?P<{name}>{regex})" for name, regex in tokens)
pattern = re.compile(regex)


def parse(s: str) -> list[Sexp]:
    """
    Parse an s-expression

    >>> parse("(foo (bar X Y) Z); yoyoyo \\n (foo)")
    [['foo', ['bar', 'X', 'Y'], 'Z'], ['foo']]
    >>> parse(" \
    (define-const x Int) \
    (define-fun f ((a Int) (b Int)) Int) \
    (assert (= (f x 3) 4 4.7)) \
    (check-sat) \
    ")
    [['define-const', 'x', 'Int'], 
     ['define-fun', 'f', [['a', 'Int'], ['b', 'Int']], 'Int'], 
     ['assert', ['=', ['f', 'x', 3], 4, 4.7]], 
     ['check-sat']]
    >>> parse("(-17)")
    [[-17]]
    >>> parse("(- 1 2 3 -3.6)")
    [['-', 1, 2, 3, -3.6]]
    >>> parse("(foo @@@)")
    Traceback (most recent call last):
     ...
    ValueError: ('unexpected characters', '@@@', '(foo @@@)')
    """

    def tokens():
        curr = 0
        for match_ in pattern.finditer(s):
            # Check for skipped characters
            if match_.start() != curr:
                raise ValueError(
                    "unexpected characters",
                    s[curr : match_.start()],
                    s[max(0, curr - 40) : min(curr + 40, len(s))],
                )
            curr = match_.end()
            match match_.lastgroup:
                case "WS" | "COMMENT":
                    continue
                case _:
                    yield match_

    it = tokens()

    def sexp():
        # opening "(" is assumed already consumed
        items = []
        for match_ in it:
            match match_.lastgroup:
                case "LPAREN":
                    items.append(sexp())
                case "RPAREN":
                    return items
                case "IDENT":
                    items.append(match_.group())
                case "NUMBER":
                    val = match_.group()
                    items.append(int(val) if "." not in val else float(val))
                # case "QUOTE":
                #    raise NotImplementedError("quote", match_)
                case _:
                    raise NotImplementedError(match_)
        raise ValueError("unbalanced paren")

    # match sexp*
    out = []
    for match_ in it:
        match match_.lastgroup:
            case "LPAREN":
                out.append(sexp())
            case "RPAREN":
                raise ValueError("unbalanced paren", match_)
            case _:
                raise ValueError("expected (", match_)
    return out


def pprint_sexp(sexp: Sexp) -> str:
    """
    Pretty print a single s-expression

    >>> sexp = parse("(foo (bar X Y) Z); yoyoyo \\n (foo)")[0]
    >>> pprint_sexp(sexp)
    '(foo (bar X Y) Z)'
    """
    if isinstance(sexp, list):
        return "(" + " ".join(pprint_sexp(s) for s in sexp) + ")"
    else:
        return str(sexp)


def pprint_sexps(sexps: list[Sexp]) -> str:
    """
    Pretty print s-expressions

    >>> sexps = parse("(foo (bar X Y) Z); yoyoyo \\n (foo)")
    >>> print(pprint_sexps(sexps))
    (foo (bar X Y) Z)
    (foo)
    """
    return "\n".join(map(pprint_sexp, sexps))
