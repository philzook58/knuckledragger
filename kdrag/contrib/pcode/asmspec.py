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


@dataclass
class BoolStmt:
    label: str
    addr: int
    expr: smt.BoolRef


class Assert(BoolStmt): ...


class Assume(BoolStmt): ...


class Exit(BoolStmt): ...


class Entry(BoolStmt): ...


class Cut(BoolStmt): ...


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


class TraceState(NamedTuple):
    start: SpecStmt
    trace: list[int]  # list of addresses
    state: pcode.SimState


class VerificationCondition(NamedTuple):
    start: SpecStmt
    trace: list[int]
    path_cond: list[smt.BoolRef]
    memstate: pcode.MemState
    cause: SpecStmt
    # pf : Optional[kd.Proof] = None

    def __repr__(self):
        return f"VC({self.start}, {[hex(addr) for addr in self.trace]}, {self.cause})"

    def verify(self, ctx: pcode.BinaryContext, by=[]) -> kd.Proof:
        """
        Verify the verification condition using the given context.
        """
        vc = smt.Implies(
            smt.And(*self.path_cond),
            ctx.substitute(self.memstate, self.cause.expr),
        )
        return kd.prove(vc, by=by)


def execute_spec_stmts(
    stmts: list[SpecStmt], tracestate: TraceState
) -> tuple[Optional[TraceState], list[VerificationCondition]]:
    trace, state = tracestate.trace, tracestate.state
    vcs = []
    for stmt in stmts:
        if isinstance(stmt, Assume) or isinstance(stmt, Entry):
            # Add the assumption to the path condition
            state = dataclasses.replace(
                state,
                path_cond=state.path_cond + [stmt.expr],
            )
        elif (
            isinstance(stmt, Assert) or isinstance(stmt, Exit) or isinstance(stmt, Cut)
        ):
            vcs.append(
                VerificationCondition(
                    tracestate.start,
                    trace.copy(),
                    state.path_cond.copy(),
                    state.memstate,
                    stmt,
                )
            )
            if isinstance(stmt, Exit) or isinstance(stmt, Cut):
                # If this is an exit or cut, we end the execution of this path
                return None, vcs
        else:
            raise Exception(
                f"Unexpected statement type {type(stmt)} in execute_specstmts"
            )
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
        TraceState(tracestate.start, tracestate.trace + [state0.pc[0]], state)
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
        for n, stmt in enumerate(specstmts):
            if isinstance(stmt, Cut) or isinstance(stmt, Entry):
                precond = ctx.substitute(mem, stmt.expr)
                assert isinstance(precond, smt.BoolRef)
                tracestate = TraceState(
                    start=stmt,
                    trace=[],
                    state=pcode.SimState(mem, (addr, 0), [precond]),
                )
                tracestate, new_vcs = execute_spec_stmts(specstmts[n + 1 :], tracestate)
                vcs.extend(new_vcs)
                if tracestate is not None:
                    todo.extend(execute_insn(tracestate, ctx, verbose=verbose))
    # Execute pre specstmts and instructions
    while todo:
        tracestate = todo.pop()
        addr = tracestate.state.pc[0]
        specstmts = spec.addrmap.get(addr, [])
        tracestate, new_vcs = execute_spec_stmts(specstmts, tracestate)
        vcs.extend(new_vcs)
        if tracestate is not None:
            todo.extend(execute_insn(tracestate, ctx, verbose=verbose))
    return vcs


@dataclass
class Results:
    successes: list[str] = dataclasses.field(default_factory=list)
    failures: list[str] = dataclasses.field(default_factory=list)


def assemble_and_gen_vcs(
    filename: str, langid="x86:LE:64:default", as_bin="as"
) -> tuple[pcode.BinaryContext, list[VerificationCondition]]:
    subprocess.run([as_bin, filename, "-o", "/tmp/kdrag_temp.o"], check=True)
    ctx = pcode.BinaryContext("/tmp/kdrag_temp.o", langid=langid)
    spec = AsmSpec.of_file(filename, ctx)
    return ctx, run_all_paths(ctx, spec)


def assemble_and_check(
    filename: str, langid="x86:LE:64:default", as_bin="as"
) -> Results:
    ctx, vcs = assemble_and_gen_vcs(filename, langid, as_bin)
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
