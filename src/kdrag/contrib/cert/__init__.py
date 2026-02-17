import kdrag.kernel as kernel
import kdrag.smt as smt
import kdrag as kd

"""
We aren't using bool sort as proof objects because that is semantically meaningful.
We're doing it because SMTLIB has nice support for multi-arity boolean functions.

Hmm. Should we have just been storing proofs in z3 ast all along?
Well, that costs extra z3 calls for every proof and you may not need to be serializing.
Better to hold that off for a long exporting event.
"""

export = smt.Function("kd_export", smt.BoolSort(), smt.BoolSort())

# argument 1 is thm, argument 2 is `and` or further proof objects in by
prove = smt.Function("kd_prove", smt.BoolSort(), smt.BoolSort(), smt.BoolSort())
axiom = smt.Function("kd_axiom", smt.BoolSort(), smt.BoolSort())
define = smt.Function("kd_define", smt.BoolSort(), smt.BoolSort())


def serialize_proof(proof: kernel.Proof) -> str:
    """

    >>> x = smt.Int("x")
    >>> assert "(assert (kd_export (kd_prove (= (+ x 1) (+ 1 x)) true)))" in serialize_proof(kernel.prove(x + 1 == 1 + x))
    >>> z = kernel.define("z", [], smt.IntVal(42))
    >>> _ = serialize_proof(kernel.prove(z > 0, by=[z.defn]))
    """
    assert isinstance(proof, kernel.Proof)
    mapping = {}

    def worker(p):
        id = p.thm.get_id()
        if id in mapping:  # memoization
            return mapping[id]
        else:
            match p.reason:
                case ["prove", *by]:
                    if len(by) == 0:
                        pf = prove(p.thm, smt.BoolVal(True))
                    else:
                        pf = prove(p.thm, smt.And([worker(b) for b in by]))
                case ["axiom", *_data]:
                    pf = axiom(p.thm)
                case "definition":  # TODO: should probably wrap this
                    pf = define(p.thm)
                case _:
                    raise ValueError(f"Unknown proof reason: {p.reason}")
            mapping[id] = pf
            return pf

    s = smt.Solver()
    s.add(export(worker(proof)))
    return s.sexpr()
    # return worker(proof).serialize()


def deserialize_proof(st: str) -> kernel.Proof:
    """ """
    s = smt.Solver()
    s.from_string(st)
    if len(s.assertions()) != 1:
        raise Exception("single assertion expected")
    fml = s.assertions()[0]
    if fml.decl() != export:
        raise Exception("export expected")
    pf = fml.arg(0)
    # pf = smt.deserialize(s)
    mapping = {}

    def worker(pf):
        id = pf.get_id()
        if id in mapping:
            return mapping[id]
        else:
            decl = pf.decl()
            if decl == prove:
                thm, by = pf.children()
                if smt.is_true(by):
                    by = []
                elif smt.is_and(by):
                    by = [worker(w) for w in by.children()]
                else:
                    raise ValueError(f"Unexpected proof object in by: {by.decl()}")
                pf = kernel.prove(thm, by=by)
            elif decl == axiom:
                thm = pf.arg(0)
                pf = kernel.axiom(thm)
            elif decl == define:
                thm = pf.arg(0)
                assert isinstance(thm, smt.QuantifierRef) and thm.is_forall()
                vs, body = kd.utils.open_binder_unhygienic(thm)
                vids = {v.get_id() for v in vs}
                assert smt.is_eq(body)
                lhs, rhs = body.children()
                assert smt.is_app(lhs) and all(
                    v.get_id() in vids for v in lhs.children()
                )
                f = kd.define(lhs.decl().name(), vs, rhs)
                pf = f.defn
            else:
                raise ValueError(f"Unknown proof object decl: {decl}")
        mapping[id] = pf
        return pf

    return worker(pf)
