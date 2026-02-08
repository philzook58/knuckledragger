import kdrag.smt as smt
from dataclasses import dataclass
import kdrag as kd
from typing import Optional


@dataclass
class OpenDefn:
    """
    An Open Definition. This is sound to because it is implemented as an if-then-else chain where we are adding definitions
    to previously undefined cases. There is a floppy tail kept at the end  of the chain.

    This is debatably a new axiom schema. It only uses `kd.define`, but unusual uses of kd.define have the force of a new axiom.

    >>> d = OpenDefn("f9023", smt.IntSort(), smt.IntSort())
    >>> f = d.decl()
    >>> x = smt.Int("x")
    >>> d.define([x], x < 0, -x)
    >>> kd.full_simp(f(-5))
    5
    >>> kd.full_simp(f(5)) # undefined. Reaches end of current chain so can't be simplified further
    f90231(5)
    >>> d.define([x], x >= 0, x + 1)
    >>> kd.full_simp(f(5))
    6
    >>> d.define([x], x == 0, 42) # covered by previous case, so is irrelevant
    >>> kd.full_simp(f(0))
    1
    """

    name: str
    fs: list[smt.FuncDeclRef]
    sorts: tuple[smt.SortRef, ...]

    def __init__(self, name, *sorts):
        self.name = name
        self.sorts = sorts
        self.fs = [smt.Function(name, *sorts)]  # kd.reserve?

    def decl(self):
        return self.fs[0]

    def define(self, args, precond, body):
        f = self.fs[-1]
        new_f = smt.Function(self.name + str(len(self.fs)), *self.sorts)  # kd.reserve?
        f = kd.define(f.name(), args, smt.If(precond, body, new_f(*args)))
        self.fs[-1] = f
        self.fs.append(new_f)

    def __call__(self, *args):
        return self.decl()(*args)


@dataclass
class RefinedDefn:
    """
    EXPERIMENTAL IDEA. DO NOT USE

    This is using an is_sat judgement rather than an is_valid judgement.
    It only somewhat protects you from inconsistency.

    It is very possible for multiple undefined values to be refined such that their axioms are not
    consistent



    >>> r = RefinedDefn("g123", smt.IntSort())
    >>> g123 = r.decl()
    >>> r.refine(g123 > 0)
    >>> r.refine(g123 > 1)
    >>> r.property
    |= And(And(True, g123 > 0), g123 > 1)
    >>> r.refine(g123 < 0)
    Traceback (most recent call last):
    ...
    ValueError: Refinement is inconsistent
    """

    decl: smt.FuncDeclRef
    _property: kd.kernel.Proof

    # The decl doesn't really matter.
    def __init__(self, name: str, *sorts: tuple[smt.SortRef, ...]):
        self.decl = smt.Function(name, *sorts)
        self._property = kd.prove(smt.BoolVal(True))

    @property
    def property(self):
        return self._property

    """
    def refine_model(self, newprop, args, model_f_body):
        new_property = smt.And(self._property.thm, newprop)
        prop_of_model = smt.substitute_funs(smt.And(new_property, [self.decl, smt.Lambda(args), body].body())
        s = smt.Solver()
        s.add(prop_of_model)
        res = s.check()
        if res == smt.sat:
            self._property = kd.axiom(new_property)
        else:
            raise ValueError("Refinement has not been shown to be consistent with previous properties")
    """

    def refine(self, newprop: smt.BoolRef, example: Optional[smt.BoolRef] = None):
        s = smt.Solver()
        s.add(self._property.thm)
        s.add(newprop)
        if example is not None:
            s.add(example)
        res = s.check()
        if res == smt.sat:
            # There is a model of the decl with all these "definitional" properties.
            self._property = kd.axiom(smt.And(self._property.thm, newprop))
        elif res == smt.unsat:
            raise ValueError("Refinement is inconsistent")
        else:
            raise ValueError(
                "Refinement has not been shown to be consistent with previous properties",
                newprop,
            )
