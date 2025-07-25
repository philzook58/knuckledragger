"""
Hoare Logic over the python AST.

This is not an attempt to properly model the python semantics.
Instead it is interpreting the python ast as a simple typed imperative language.

See:
- https://en.wikipedia.org/wiki/Hoare_logic
- https://softwarefoundations.cis.upenn.edu/plf-current/Hoare.html
- https://en.wikipedia.org/wiki/Predicate_transformer_semantics
"""

from dataclasses import dataclass
import ast
import kdrag.smt as smt
import kdrag as kd
import kdrag.reflect


@dataclass(frozen=True)
class Hoare:
    """
    Constructing the Hoare class is consider to be a proof. It should only be constructed through it's trusted smart constructors.
    It is analogous to a kd.Proof object in this sense.
    Using the bare constructor is analogous to asserting an axiom. Possibly useful, but at your own risk.

    Alternative approaches may include:
    - Shallowly embedding an operational semantics inside z3
    - Deeply embedding a python AST in z3 and defining an interpreter for it.

    This is lighter weight than that, borrowing on useful existing facilities.
    """

    pre: smt.BoolRef
    cmds: tuple[ast.AST, ...]
    post: smt.BoolRef
    reasons: list

    def __repr__(self):
        return f"{{{self.pre}}} {'; '.join(ast.unparse(cmd) for cmd in self.cmds)} {{{self.post}}}"

    @classmethod
    def skip(cls, P: smt.BoolRef):
        """
        Create a Hoare triple for a skip command.

        -------------- skip
        {P} skip {P}
        """
        assert isinstance(P, smt.BoolRef), "P must be a BoolRef"
        return cls(P, (ast.Pass(),), P, ["skip"])

    @classmethod
    def assign(cls, cmd: ast.Assign, P: smt.BoolRef):
        """
        Create a Hoare triple for an assignment command.

        ------------------- assign
        {P[e/x]} x = e {P}

        """
        assert isinstance(P, smt.BoolRef), "P must be a BoolRef"
        match cmd:
            case ast.Assign(targets=[ast.Name(id=x, ctx=ast.Store())], value=e):
                e = kdrag.reflect.expr(
                    ast.unparse(e), locals={k: smt.Int(k) for k in "x y z".split()}
                )  # TODO: We need to thread locals.
                x = smt.Const(x, e.sort())
                return cls(smt.substitute(P, (x, e)), (cmd,), P, ["assign"])
            case _:
                raise ValueError(f"Unsupported assignment: {ast.unparse(cmd)}")

    @classmethod
    def ite(cls, cmd: ast.If, hoare_body: "Hoare", hoare_orelse: "Hoare"):
        assert isinstance(hoare_body, Hoare), "true_branch must be a Hoare"
        assert isinstance(hoare_orelse, Hoare), "false_branch must be a Hoare"
        assert hoare_body.post.eq(hoare_orelse.post), "Postconditions must match"
        match cmd:
            case ast.If(test=test, body=body, orelse=orelse):
                assert body == hoare_body.cmds, "Body must match hoare_body"
                assert orelse == hoare_orelse.cmds, "Else must match hoare"
                test = kdrag.reflect.expr(
                    ast.unparse(test), locals={k: smt.Int(k) for k in "x y z".split()}
                )
                p1 = kd.prove(smt.Implies(hoare_body.pre, test))
                p2 = kd.prove(smt.Implies(hoare_orelse.pre, smt.Not(test)))
                return Hoare(
                    smt.Or(hoare_body.pre, hoare_orelse.pre),
                    (cmd,),
                    hoare_body.post,
                    ["ite", hoare_body, hoare_orelse, p1, p2],
                )
            case _:
                raise ValueError(f"Hoare.ite expected if statement: {ast.unparse(cmd)}")

    def __matmul__(self, other: "Hoare") -> "Hoare":
        """
        Compose two Hoare triples.

        {P} S1 {Q1}   {Q1} S2 {Q2}
        ------------------------------ compose
                {P} S1; S2 {Q2}

        """
        if not self.post.eq(other.pre):
            raise ValueError(
                f"Postcondition {self.post} does not match precondition {other.pre}"
            )
        assert isinstance(other, Hoare), "other must be a Hoare"
        return Hoare(
            self.pre, (self.cmds + other.cmds), other.post, ["seq", self, other]
        )

    def strengthen_pre(self, P1: smt.BoolRef, by=[]) -> "Hoare":
        """
        Strengthen the precondition of this Hoare triple.

        {P} S {Q}   P1 => P
        --------------------  strengthen_pre
            {P1} S {Q}

        >>> x = smt.Int("x")
        >>> Hoare.skip(x > 0).strengthen_pre(x > 1)
        {x > 1} pass {x > 0}
        """
        assert isinstance(P1, smt.BoolRef), "P must be a BoolRef"
        pf = kd.prove(smt.Implies(P1, self.pre), by=by)
        return Hoare(
            P1, self.cmds, self.post, self.reasons + ["strengthen_pre", P1, pf]
        )

    def weaken_post(self, Q1: smt.BoolRef, by=[]) -> "Hoare":
        """
        Weaken the postcondition of this Hoare triple.

        {P} S {Q}   Q => Q1
        --------------------  weaken_post
             {P} S {Q1}

        >>> x = smt.Int("x")
        >>> Hoare.skip(x > 0).weaken_post(x >= 0)
        {x > 0} pass {x >= 0}
        """
        assert isinstance(Q1, smt.BoolRef), "P must be a BoolRef"
        pf = kd.prove(smt.Implies(self.post, Q1), by=by)
        return Hoare(self.pre, self.cmds, Q1, self.reasons + ["weaken_post", Q1, pf])


def wp(stmt: ast.AST, P: smt.BoolRef) -> Hoare:
    """
    Weakest precondition for a statement `stmt` with postcondition `P`.
    The Hoare class is a declarative Proof object.
    `wp` infers a useful a useful Hoare triple for a program and postcondition.
    """
    match stmt:
        case ast.Assign():
            return Hoare.assign(stmt, P)
        case ast.Pass():
            return Hoare.skip(P)
        case ast.Module(body=stmts):
            return wps(stmts, P)
        case _:
            raise ValueError(f"Unsupported statement type: {ast.unparse(stmt)}")


def wps(stmts: list[ast.stmt], P: smt.BoolRef) -> Hoare:
    hoare = wp(stmts[-1], P)
    for stmt in reversed(stmts[:-1]):
        hoare = wp(stmt, P) @ hoare
        P = hoare.pre
    return hoare


def wp_str(s: str, P: smt.BoolRef) -> Hoare:
    """
    Compute the weakest precondition for a string of Python code `s` with postcondition `P`.

    >>> x,y,z = smt.Ints("x y z")
    >>> wp_str("x = 3; y = x + 2; z = y + 1", y > 0)
    {3 + 2 > 0} x = 3; y = x + 2; z = y + 1 {y > 0}
    """
    tree = ast.parse(s)
    return wps(tree.body, P)
