import re
import kdrag.smt as smt
import kdrag as kd
import dataclasses
from dataclasses import dataclass
import kdrag.contrib.pcode as pcode
from collections import defaultdict
import json
import subprocess
from typing import NamedTuple, Optional

kd_macro = r"""
#precondition
.macro kd_entry label smt_bool
\label :
.endm

.macro kd_assert label smt_bool
\label :
.endm

.macro kd_assume label smt_bool
\label :
.endm

#postcondition
.macro kd_exit label smt_bool 
\label :
.endm

#invariant
.macro kd_cut label smt_bool
\label :
.endm 

.macro kd_always smt_bool
.endm

.macro kd_prelude smt_command
.endm
"""


# mapping from address to list of (label, expr)
type AddrMap = defaultdict[int, list[tuple[str, smt.BoolRef]]]


@dataclass
class BoolEvent:
    label: str
    addr: int
    expr: smt.BoolRef


class Assert(BoolEvent): ...


class Assume(BoolEvent): ...


class Exit(BoolEvent): ...


class Entry(BoolEvent): ...


class Cut(BoolEvent): ...


type SpecStmt = Entry | Assert | Assume | Exit | Cut


@dataclass
class AsmSpec:
    """
    A specification of an assembly program.
    https://www.philipzucker.com/assembly_verify/
    Registers are named by their corresponding names in pypcode.
    You can examine them by

    ```python
    import pypcode
    print(pypcode.Context("x86:LE:64:default").registers)
    ```

    """

    addrmap: defaultdict[int, list[SpecStmt]] = dataclasses.field(
        default_factory=lambda: defaultdict(list)
    )

    @classmethod
    def of_file(cls, filename: str, ctx: pcode.BinaryContext):
        pattern = re.compile(
            r"""^\s*
                (kd_assert|kd_assume|kd_exit|kd_entry|kd_cut)
                \s+([A-Za-z_.$][A-Za-z0-9_.$]*) # valid GAS label
                \s*(?:,\s*)?                         # optional comma
                "([^"]+)"                        # quoted formula
                \s*$""",
            re.VERBOSE,
        )
        # prelude_pattern = re.compile("^\.kd_prelude\s+([^;]+);?\s*$")
        preludes = []
        decls = ctx._subst_decls.copy()
        decls["ram"] = smt.Array("ram", smt.BitVecSort(64), smt.BitVecSort(8))
        spec = cls()
        with open(filename) as f:
            for lineno, line in enumerate(f.readlines()):
                match = pattern.match(line)
                if match:
                    cmd, label, expr = match.groups()
                    assert ctx.loader is not None, (
                        "BinaryContext must be loaded before disassembling"
                    )
                    sym = ctx.loader.find_symbol(label)
                    if sym is None:
                        raise Exception(
                            f"Symbol {label} as line {lineno} not found in binary {ctx.filename}"
                        )
                    else:
                        addr = sym.rebased_addr
                    smt_string = "\n".join(preludes + ["(assert ", expr, ")"])
                    expr = smt.parse_smt2_string(smt_string, decls=decls)[0]
                    if cmd == "kd_entry":
                        spec.addrmap[addr].append(Entry(label, addr, expr))
                    elif cmd == "kd_assert":
                        spec.addrmap[addr].append(Assert(label, addr, expr))
                    elif cmd == "kd_assume":
                        spec.addrmap[addr].append(Assume(label, addr, expr))
                    elif cmd == "kd_exit":
                        spec.addrmap[addr].append(Exit(label, addr, expr))
                    elif cmd == "kd_cut":
                        spec.addrmap[addr].append(Cut(label, addr, expr))
        return spec

    def __repr__(self):
        return json.dumps(
            dataclasses.asdict(self), indent=2, default=lambda b: b.sexpr()
        )


@dataclass
class Results:
    successes: list[str] = dataclasses.field(default_factory=list)
    failures: list[str] = dataclasses.field(default_factory=list)
    traces: list[object] = dataclasses.field(default_factory=list)


class VerificationCondition(NamedTuple):
    start: SpecStmt
    trace: list[tuple[int, int]]
    path_cond: list[smt.BoolRef]
    memstate: pcode.MemState
    cause: SpecStmt

    def __repr__(self):
        return (
            f"VC({self.start}, {[hex(addr) for addr, pc in self.trace]}, {self.cause})"
        )

    # pf : Optional[kd.Proof] = None
    def verify(self, ctx: pcode.BinaryContext, by=[]) -> kd.Proof:
        """
        Verify the verification condition using the given context.
        """
        vc = smt.Implies(
            smt.And(*self.path_cond),
            ctx.substitute(self.memstate, self.cause.expr),
        )
        return kd.prove(vc, by=by)


class TraceState(NamedTuple):
    start: SpecStmt
    trace: list[tuple[int, int]]  # list of (addr, pc)
    state: pcode.SimState


def execute_specstmts(
    events: list[SpecStmt], tracestate: TraceState
) -> tuple[Optional[TraceState], list[VerificationCondition]]:
    trace, state = tracestate.trace, tracestate.state
    vcs = []
    for e in events:
        if isinstance(e, Assume) or isinstance(e, Entry):
            # Add the assumption to the path condition
            state = dataclasses.replace(
                state,
                path_cond=state.path_cond + [e.expr],
            )
        elif isinstance(e, Assert) or isinstance(e, Exit) or isinstance(e, Cut):
            vcs.append(
                VerificationCondition(
                    tracestate.start,
                    trace.copy(),
                    state.path_cond.copy(),
                    state.memstate,
                    e,
                )
            )
            if isinstance(e, Exit) or isinstance(e, Cut):
                # If this is an exit or cut, we end the execution of this path
                return None, vcs
        else:
            raise Exception(f"Unexpected event type {type(e)} in execute_specstmts")
    return TraceState(tracestate.start, trace, state), vcs


def execute_insn(
    tracestate: TraceState, ctx: pcode.BinaryContext, verbose=True
) -> list[TraceState]:
    # TODO : copy trace less. if single result
    state0 = tracestate.state
    addr, pc = state0.pc
    if pc != 0:
        raise Exception(f"Unexpected program counter {pc} at address {hex(addr)}")
    return [
        TraceState(tracestate.start, tracestate.trace + [state0.pc], state)
        for state in ctx.sym_execute(
            state0.memstate,
            addr,
            path_cond=state0.path_cond,
            max_insns=1,
            verbose=verbose,
        )
    ]


def run_all_paths(
    ctx: pcode.BinaryContext, spec: AsmSpec, mem=None, verbose=True
) -> list[VerificationCondition]:
    if mem is None:
        mem = pcode.MemState.Const("mem")
    todo = []
    vcs = []
    # Initialize executions out of entry points and cuts
    for addr, specstmts in spec.addrmap.items():
        for n, event in enumerate(specstmts):
            if isinstance(event, Cut) or isinstance(event, Entry):
                precond = ctx.substitute(mem, event.expr)
                assert isinstance(precond, smt.BoolRef)
                tracestate = TraceState(
                    start=event,
                    trace=[],
                    state=pcode.SimState(mem, (addr, 0), [precond]),
                )
                tracestate, new_vcs = execute_specstmts(specstmts[n + 1 :], tracestate)
                vcs.extend(new_vcs)
                if tracestate is not None:
                    todo.extend(execute_insn(tracestate, ctx, verbose=verbose))
    # Execute pre specstmts and instructions
    while todo:
        tracestate = todo.pop()
        addr = tracestate.state.pc[0]
        specstmts = spec.addrmap.get(addr, [])
        tracestate, new_vcs = execute_specstmts(specstmts, tracestate)
        vcs.extend(new_vcs)
        if tracestate is not None:
            todo.extend(execute_insn(tracestate, ctx, verbose=verbose))
    return vcs


'''
def run_all_paths0(
    ctx: pcode.BinaryContext,
    spec: AsmSpec,
    mem=None,
    verbose=True,
    by: list[kd.Proof] = [],
) -> Results:
    if mem is None:
        mem = pcode.MemState.Const("mem")  # ctx.init_mem() very slow
    todo: list[TraceState] = []
    res = Results([], [])
    if len(spec.entries) == 0:
        raise Exception("No entry points found in the assembly specification")
    # Initialize executions out of entry points and cuts
    for addr, events in spec.addrmap.items():
        for event in events:
            if isinstance(event, Cut) or isinstance(event, Entry):
                precond = ctx.substitute(mem, event.expr)
                assert isinstance(precond, smt.BoolRef)
                todo.append(TraceState([], pcode.SimState(mem, (addr, 0), [precond])))
    """
    for addr, label_preconds in spec.entries.items():
        for label, precond in label_preconds:
            if verbose:
                print(f"entry {label} at {addr} with precond {precond}")
            precond = ctx.substitute(mem, precond)
            assert isinstance(precond, smt.BoolRef)
            todo.append(TraceState([], pcode.SimState(mem, (addr, 0), [precond])))
    for addr, label_preconds in spec.cuts.items():
        for label, invariant in label_preconds:
            if verbose:
                print(f"cut {label} at {addr} with invariant {invariant}")
            invariant = ctx.substitute(mem, invariant)
            assert isinstance(invariant, smt.BoolRef)
            todo.append(TraceState([], pcode.SimState(mem, (addr, 0), [invariant])))
    """

    def verif(state: pcode.SimState, prop: smt.BoolRef) -> kd.Proof:
        return kd.prove(
            smt.Implies(
                smt.And(*state.path_cond), ctx.substitute(state.memstate, prop)
            ),
            by=by,
        )

    while todo:
        tracestate = todo.pop()
        trace, state = tracestate.trace, tracestate.state
        addr, pc = state.pc
        if pc != 0:  # We don't support intra instruction assertions
            raise Exception(f"Unexpected program counter {pc} at address {hex(addr)}")
        # check assert conditions
        for addr, events in spec.addrmap.get():
            for event in events:
                if isinstance(event, Assume):
                    state = dataclasses.replace(
                        state,
                        path_cond=state.path_cond
                        + [ctx.substitute(state.memstate, event.expr)],
                    )
                    # TODO add trace
                if (
                    isinstance(event, Assert)
                    or isinstance(event, Exit)
                    or (isinstance(event, Cut) and len(trace) != 0)
                ):
                    try:
                        _pf = verif(state, event.expr)
                        msg = f"[✅] {type(event)} {event.label}: {event.expr}"
                        print(msg)
                        trace.append(msg)
                        res.successes.append(msg)
                    except Exception as e:
                        msg = f"[❌] Error proving {event.label}: {event.expr}"
                        print(msg, e)
                        trace.append(msg)
                        res.failures.append(msg)
        if addr in spec.asserts:
            for label, _assert in spec.asserts[addr]:
                try:
                    _pf = verif(state, _assert)
                    msg = f"[✅] assert {label}: {_assert}"
                    res.successes.append(msg)
                    trace.append(msg)
                except Exception as e:
                    msg = f"[❌] Error proving assert {label}: {_assert}"
                    res.failures.append(msg)
                    trace.append(msg)
                    print("[❌] Error proving assert", label, _assert, e)
                    # raise e
                # maybe prove form (state == current state => assert_expr)
        # If address is an exit or cut, we check postcondition and end the execution of this path
        # The first time we encounter a cut is at the start of the path
        if addr in spec.exits or (addr in spec.cuts and len(trace) != 0):
            for label, _exit in spec.exits[addr]:
                try:
                    _pf = verif(state, _exit)
                    msg = f"[✅] exit {label}: {_exit}"
                    print(f"[✅] exit {label}: {_exit}")
                    trace.append(msg)
                    res.successes.append(f"[✅] exit {label}: {_exit}")
                except Exception as e:
                    print("[❌] Error proving exit", label, _exit, e)
                    msg = f"[❌] Error proving exit {label}: {_exit}"
                    trace.append(msg)
                    res.failures.append(msg)
            for label, _cut in spec.cuts[addr]:
                try:
                    _pf = verif(state, _cut)
                    msg = f"[✅] cut {label}: {_cut}"
                    print(f"[✅] cut {label}: {_cut}")
                    trace.append(msg)
                    res.successes.append(f"[✅] cut {label}: {_cut}")
                except Exception as e:
                    print("[❌] Error proving cut", label, _cut, e)
                    msg = f"[❌] Error proving cut {label}: {_cut}"
                    trace.append(msg)
                    res.failures.append(msg)
            res.traces.append(trace)
            continue  # Do not put back on todo
        # If address is an assume, we add the assumption to the path condition
        if addr in spec.assumes:
            for label, _assume in spec.assumes[addr]:
                state = dataclasses.replace(
                    state,
                    path_cond=state.path_cond
                    + [ctx.substitute(state.memstate, _assume)],
                )
        # Regular execution
        trace.append((addr, pc))
        todo.extend(
            [
                TraceState(trace.copy(), state)
                for state in ctx.sym_execute(
                    state.memstate,
                    addr,
                    path_cond=state.path_cond,
                    max_insns=1,
                    verbose=verbose,
                )
            ]
        )
    return res
'''


def assemble_and_check(
    filename: str, langid="x86:LE:64:default", as_bin="as"
) -> Results:
    subprocess.run([as_bin, filename, "-o", "/tmp/kdrag_temp.o"], check=True)
    ctx = pcode.BinaryContext("/tmp/kdrag_temp.o", langid=langid)
    spec = AsmSpec.of_file(filename, ctx)
    print(spec)
    vcs = run_all_paths(ctx, spec)
    res = Results()
    for vc in vcs:
        try:
            vc.verify(ctx)
            res.successes.append(f"[✅] {vc}")
        except Exception as _e:
            res.failures.append(f"[❌] {vc}")
    return res


def assemble_and_check_str(asm_str: str) -> Results:
    with open("/tmp/kdrag_temp.s", "w") as f:
        f.write(asm_str)
        f.flush()
    return assemble_and_check("/tmp/kdrag_temp.s")
