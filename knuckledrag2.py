import tempfile
import subprocess


class Term():
    def __eq__(self, rhs):
        return Eq(self, rhs)

    def __add__(self, rhs):
        return Function("+", [self, rhs])

    def __sub__(self, rhs):
        return Function("-", [self, rhs])


class Var(Term):
    def __init__(self, name):
        self.name = name

    def __str__(self):
        return self.name.upper()


def Vars(xs):
    return [Var(x) for x in xs.split()]


# class Sort(Enum):
#    NUMBER = auto()
#    SYMBOL = auto()
#    TERM = auto()


class Function():
    def __init__(self, name, args):
        self.name = name
        self.args = args

    def __str__(self):
        args = ",".join(map(repr, self.args))
        return "%s(%s)" % (self.name, args)

    def smt2(self):
        args = " ".join([arg.smt2() for arg in self.args])
        return "(%s %s)" % (self.name, args)


class Formula():
    def __and__(self, rhs):
        return And([self, rhs])

    def __le__(self, rhs):
        return Impl(rhs, self)

    def __gt__(self, rhs):
        return Impl(self, rhs)

    def __or__(self, rhs):
        return Or([self, rhs])

    def __invert__(self):
        return Not(self)


class Atom(Formula):
    def __init__(self, name, args):
        self.name = name
        self.args = args

    def __str__(self):
        if len(self.args) > 0:
            args = ",".join(map(str, self.args))
            return "%s(%s)" % (self.name, args)
        else:
            return self.name


def Const(name):
    return Atom(name, [])


def Consts(names):
    return [Const(name) for name in names.split()]


class Eq(Formula):
    def __init__(self, lhs, rhs):
        self.lhs = lhs
        self.rhs = rhs

    def __str__(self):
        return "(%s = %s)" % (str(self.lhs), str(self.rhs))


class And(Formula):
    def __init__(self, val):
        self.val = val

    def __str__(self):
        t = " & ".join([str(val) for val in self.val])
        return "(%s)" % t


class Or(Formula):
    def __init__(self, val):
        self.val = val

    def __str__(self):
        t = " | ".join([str(val) for val in self.val])
        return "(%s)" % t


class Impl(Formula):
    def __init__(self, hyp, conc):
        self.hyp = hyp
        self.conc = conc

    def __str__(self):
        return "(%s => %s)" % (str(self.hyp), str(self.conc))


class ForAll(Formula):
    def __init__(self, vars, body):
        self.vars = vars
        self.body = body

    def __str__(self):
        vars = ",".join([str(var) for var in self.vars])
        return "(! [%s] : %s)" % (vars, str(self.body))


class Exists(Formula):
    def __init__(self, vars, body):
        self.vars = vars
        self.body = body

    def __str__(self):
        vars = ",".join([str(var) for var in self.vars])
        return "(? [%s] : %s)" % (vars, str(self.body))


class Not(Formula):
    def __init__(self, val):
        self.val = val

    def __str__(self):
        return "(~ %s)" % str(self.val)


class Solver():
    def __init__(self):
        self.facts = {}

    def add(self, x, name=None):
        assert isinstance(x, Formula)
        if name == None:
            name = "myaxiom_%d" % len(self.facts)
        self.facts[name] = x

    def solve(self, execname="vampire"):
        facts = ["fof(%s, axiom, %s)." % (name, str(fact)) for name,
                 fact in self.facts.items()]
        print(facts)
        with tempfile.NamedTemporaryFile(suffix=".tptp") as fp:
            fp.writelines([stmt.encode() + b"\n" for stmt in facts])
            fp.flush()
            res = subprocess.check_output(
                [execname, fp.name])
            print(str(res))
        return res
        # writetotemp file. Call vampire.


x, y, z = Vars("x y z")
def path(x, y): return Atom("path", [x, y])
def edge(x, y): return Atom("edge", [x, y])


a, b, c = Consts("a b c")

s = Solver()
s.add(edge(a, b))
s.add(edge(b, c))
s.add(ForAll([x, y], path(x, y) <= edge(x, y)))
s.add(ForAll([x, y], edge(x, y) > path(x, y)))
s.add(ForAll([x, y, z], path(x, z) <= (edge(x, y) & path(y, z))))
s.solve(execname="vampire")


class Proof(object):
    def __init__(self, formula, DO_NOT_USE_trusted=False, reason=None):
        if DO_NOT_USE_trusted:
            # I should deep copy formula and or/make formula immutable
            # make getter of formula for iy to be immutable
            # Could also serialize it here maybe? Strings are immutable.
            # Keep all of them. Check formula against immutable string.
            object.__setattr__(self, "formula", formula)
            object.__setattr__(self, "formula_str", str(formula))
            object.__setattr__(self, "reason", reason)
        else:
            raise Exception("Proof should only be produced via modus or axiom")

    def __setattr__(self, name, value):
        raise Exception("Attempted to set to immutable Proof object")

    def __delattr__(self, name):
        raise Exception("Attempted to delete from Proof object")

    def check_consistency(self):
        return str(self.formula) == self.formula_str

    def __repr__(self):
        return "Proof(%s)" % str(self.formula_str)


def axiom(formula):
    return Proof(formula, DO_NOT_USE_trusted=True)


def modus(conc, *hyps, sanity=True):
    # sanity checks: make sure hyps alone isn't inconsistent
    s = Solver()
    s.add(Not(conc))
    for hyp in hyps:
        assert isinstance(hyp, Proof)
        s.add(hyp.formula)
    res = s.solve(execname="vampire")
    if "SZS status Unsatisfiable" in res:
        return Proof(conc, DO_NOT_USE_trusted=True)
    else:
        raise Exception("modus failed")


ax1 = axiom(edge(a, b))
ax2 = axiom(edge(b, c))

path_base = axiom(ForAll([x, y], path(x, y) <= edge(x, y)))
path_trans = axiom(ForAll([x, y, z], path(x, z) <= (edge(x, y) & path(y, z))))

path_ac = modus(path(a, c), ax1, ax2, path_base, path_trans)
print(path_ac)


def even(x): return Atom("even", x)
def odd(x): return Atom("odd", x)


even_def = axiom(ForAll([x], even(x) == Exists([y], x=2*y)))

'''
Schema

def nat_induction(P):
    return axiom(Implies(P(zero)  & ForAll([x], P(x) > P(x + 1)), ForAll([x], P(x))))


'''

'''
Backwards proof:

def Goal():
    def self():
        self.cbs = [] # callbacks
    def back(self,*hyps, sanity=True):
        prove(self.formula, hyps)

    def intros(self):

    def exists(self): ???

    def simp()
    def rewrite()





'''
