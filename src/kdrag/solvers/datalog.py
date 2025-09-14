import kdrag.smt as smt
import kdrag.rewrite as rw
import sqlite3

"""

A simple datalog bv compiling clauses to SQL.
See snakelog https://github.com/philzook58/snakelog

Z3 also has built in datalog. https://microsoft.github.io/z3guide/docs/fixedpoints/basicdatalog/

"""


def _compile_body(
    vs: list[smt.ExprRef], body: smt.BoolRef
) -> tuple[dict, list[str], list[str]]:
    todo = [body]
    env = {}
    froms = []
    wheres = []
    counter = 0
    while todo:
        rel = todo.pop()
        if smt.is_eq(rel):
            raise ValueError("Equality not supported")  # TODO
        elif smt.is_not(rel):
            raise ValueError("Negation not supported")  # TODO
        elif smt.is_or(rel):
            raise ValueError("Disjunction not supported")  # TODO
        elif smt.is_and(rel):
            todo.extend(rel.children())
        elif smt.is_true(rel):
            continue
        elif smt.is_app(rel):
            name = rel.decl().name()
            args = rel.children()
            row_name = name + str(counter)
            counter += 1
            froms.append(f"{name} AS {row_name}")
            for n, arg in enumerate(args):
                if arg in vs:
                    if arg in env:
                        wheres.append(f"{env[arg]} = {row_name}.x{n}")
                    else:
                        env[arg] = f"{row_name}.x{n}"
                else:
                    wheres.append(f"{row_name}.x{n} = {str(arg)}")
        else:
            raise ValueError(f"Unsupported expression: {rel}")
    return env, froms, wheres


def _compile_rule(rule: rw.Rule) -> str:
    env, froms, wheres = _compile_body(rule.vs, rule.hyp)
    name = rule.conc.decl().name()
    selects = []
    for n, arg in enumerate(rule.conc.children()):
        if arg in rule.vs:
            if arg in env:
                selects.append(f"{env[arg]} AS x{n}")  # maybe select as keyword
            else:
                raise ValueError(f"Variable {arg} not found in body")
        else:
            selects.append(f"{arg} AS x{n}")
    froms = ", ".join(froms)
    wheres = " AND ".join(wheres)
    selects = ", ".join(selects)
    return f"""
    INSERT OR IGNORE INTO {name} SELECT DISTINCT {selects}
    {"FROM " + froms if froms else ""}
    {"WHERE " + wheres if wheres else ""}
    """


class Datalog:
    """
    A simple datalog solver using sqlite

    >>> import kdrag as kd
    >>> s = Datalog()
    >>> edge = smt.Function('edge', smt.IntSort(), smt.IntSort(), smt.BoolSort())
    >>> path = smt.Function('path', smt.IntSort(), smt.IntSort(), smt.BoolSort())
    >>> s.declare_sig([edge, path])
    >>> x, y, z = smt.Ints('x y z')
    >>> s.run(edge(1,2))
    >>> s.run(edge(2,3))
    >>> s.run(kd.QForAll([x,y], edge(x,y), path(x,y)))
    >>> s.run(kd.QForAll([x,y,z], edge(x,y), path(y,z), path(x,z)))
    >>> s.run(kd.QForAll([x,y,z], edge(x,y), path(y,z), path(x,z)))
    >>> s.db.execute("SELECT * FROM path").fetchall()
    [(1, 2), (2, 3), (1, 3)]
    """

    def __init__(self):
        self.db = sqlite3.connect(":memory:")

    def declare_sig(self, sig: list[smt.FuncDeclRef]):
        for f in sig:
            primkey = "(" + ", ".join([f"x{i}" for i in range(f.arity())]) + ")"
            self.db.execute(f"""CREATE TABLE IF NOT EXISTS {f.name()} 
                            ({', '.join([f'x{i} {f.range().name()}' for i in range(f.arity())])}, 
                             PRIMARY KEY {primkey})""")

    def run(self, rule: rw.Rule | smt.BoolRef):
        if isinstance(rule, smt.BoolRef):
            rule = rw.rule_of_expr(rule)
        sql = _compile_rule(rule)
        self.db.execute(sql)
