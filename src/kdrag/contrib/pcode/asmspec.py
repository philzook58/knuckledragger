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
# For injection of SMT commands, e.g., declare-const
.macro kd_prelude expr
.pushsection .asmspec,"a"
.ascii "kd_prelude \"\expr\"\n"
.popsection
.endm


.macro kd_always expr
.pushsection .asmspec,"a"
.ascii "kd_always \"\expr\"\n"
.popsection
.endm


.macro kd_boolstmt kind label expr
.pushsection .asmspec,"a"
.ascii "\kind \label \"\expr\" \n"
.popsection
\label :
.endm

# symbolic execution start points and precondition
.macro kd_entry label smt_bool
kd_boolstmt "kd_entry" \label, \smt_bool
.endm

# Assert properties
.macro kd_assert label smt_bool
kd_boolstmt "kd_assert" \label, \smt_bool
.endm

.macro kd_assume label smt_bool
kd_boolstmt "kd_assume" \label, \smt_bool
.endm

# symbolic execution end points and postcondition
.macro kd_exit label smt_bool 
kd_boolstmt "kd_entry" \label, \smt_bool
.endm

# invariant
.macro kd_cut label smt_bool
kd_boolstmt "kd_cut" \label, \smt_bool
.endm 

# For manipulation of executor ghost state. Often for saving values
.macro kd_assign label name value
.pushsection .asmspec,"a"
.ascii "kd_assign \label \name \"\value\"\n"
.popsection
\label :
.endm
"""


@dataclass
class BoolStmt:
    label: str
    addr: int
    expr: smt.BoolRef

    def __repr__(self):
        return f"{self.__class__.__name__}({self.label}, {hex(self.addr)}, {self.expr})"


class Assert(BoolStmt): ...


class Assume(BoolStmt): ...


class Exit(BoolStmt): ...


class Entry(BoolStmt): ...


class Cut(BoolStmt): ...


@dataclass
class Assign:
    label: str
    addr: int
    name: str
    expr: smt.ExprRef


@dataclass
class Always:
    expr: smt.BoolRef


@dataclass
class OutOfGas: ...


type StartStmt = Entry | Cut
type EndStmt = Assert | Exit | OutOfGas | Cut
type SpecStmt = StartStmt | EndStmt | Assume | Assign


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

    def add_entry(self, label: str, addr: int, expr: smt.BoolRef):
        self.addrmap[addr].append(Entry(label, addr, expr))

    def add_assert(self, label: str, addr: int, expr: smt.BoolRef):
        self.addrmap[addr].append(Assert(label, addr, expr))

    def add_assume(self, label: str, addr: int, expr: smt.BoolRef):
        self.addrmap[addr].append(Assume(label, addr, expr))

    def add_exit(self, label: str, addr: int, expr: smt.BoolRef):
        self.addrmap[addr].append(Exit(label, addr, expr))

    def add_cut(self, label: str, addr: int, expr: smt.BoolRef):
        self.addrmap[addr].append(Cut(label, addr, expr))

    def add_assign(self, label: str, addr: int, name: str, expr: smt.ExprRef):
        self.addrmap[addr].append(Assign(label, addr, name, expr))

    @classmethod
    def of_file(cls, filename: str, ctx: pcode.BinaryContext):
        COMMASEP = r"\s*(?:,\s*)?"
        LABEL = r"([A-Za-z_.$][A-Za-z0-9_.$]*)"  # valid GAS label
        NAME = r"([A-Za-z_.$][A-Za-z0-9_.$]*)"  # valid GAS name
        EXPR = r'"([^"]+)"'  # quoted formula
        kd_prefix = re.compile(r"^\s*kd_")
        boolstmt_pattern = re.compile(
            rf"""^\s*(kd_assert|kd_assume|kd_exit|kd_entry|kd_cut)\s+{LABEL}{COMMASEP}{EXPR}\s*$""",
        )
        assign_pattern = re.compile(
            rf"""^\s*kd_assign\s+{LABEL}\s+{NAME}\s+{EXPR}\s*$""",
        )
        prelude_pattern = re.compile(rf"^\s*kd_prelude\s+{EXPR}\s*$")
        preludes = []
        decls = ctx.state_vars.copy()
        decls["write"] = smt.Array(
            "write", smt.BitVecSort(ctx.bits), smt.BoolSort()
        ).decl()
        decls["read"] = smt.Array(
            "read", smt.BitVecSort(ctx.bits), smt.BoolSort()
        ).decl()
        spec = cls()

        def find_label(label: str) -> int:
            assert ctx.loader is not None, (
                "BinaryContext must be loaded before disassembling"
            )
            sym = ctx.loader.find_symbol(label)
            if sym is None:
                raise Exception(f"Symbol {label} not found in binary {ctx.filename}")
            return sym.rebased_addr

        def parse_smt(smt_bool: str, linemo: int, line: str) -> smt.BoolRef:
            # parse with slightly nicer error throwing, saying which line in asm responsible
            left_count, right_count = smt_bool.count("("), smt_bool.count(")")
            if left_count < right_count:
                raise ValueError(
                    f'Too many ")" parentheses in SMT expression at line {lineno + 1}: {line}'
                )
            elif left_count > right_count:
                raise ValueError(
                    f'Too many "(" parentheses in SMT expression at line {lineno + 1}: {line}'
                )
            else:
                try:
                    return smt.parse_smt2_string(smt_string, decls=decls)[0]
                except Exception as e:
                    raise Exception(
                        f"Error parsing SMT expression at line {lineno + 1}: {line}", e
                    )

        with open(filename) as f:
            for lineno, line in enumerate(f.readlines()):
                if kd_prefix.match(
                    line
                ):  # A little bit of sanity checking that we don't miss any "kd_" line
                    if match := boolstmt_pattern.match(line):
                        cmd, label, expr = match.groups()
                        addr = find_label(label)
                        smt_string = "\n".join(preludes + ["(assert ", expr, ")"])
                        expr = parse_smt(smt_string, lineno, line)
                        if cmd == "kd_entry":
                            spec.add_entry(label, addr, expr)
                        elif cmd == "kd_assert":
                            spec.add_assert(label, addr, expr)
                        elif cmd == "kd_assume":
                            spec.add_assume(label, addr, expr)
                        elif cmd == "kd_exit":
                            spec.add_exit(label, addr, expr)
                        elif cmd == "kd_cut":
                            spec.add_cut(label, addr, expr)
                    elif match := assign_pattern.match(line):
                        label, name, expr = match.groups()
                        # Turn expression `expr` into dummy assertion `expr == expr` for parsing
                        addr = find_label(label)
                        smt_string = "\n".join(
                            preludes + ["(assert (=", expr, expr, "))"]
                        )
                        expr = parse_smt(smt_string, lineno, line).arg(0)
                        spec.add_assign(label, addr, name, expr)
                    elif match := prelude_pattern.match(line):
                        expr = match.group(1)
                        preludes.append(expr)
                    else:
                        raise ValueError(
                            f"Invalid kd_ statement at line {lineno + 1}: {line}"
                        )

        return spec

    def __repr__(self):
        return json.dumps(
            dataclasses.asdict(self), indent=2, default=lambda b: b.sexpr()
        )


type Trace = list[int]  # TODO | SpecStmt


def pretty_trace(ctx: pcode.BinaryContext, trace: Trace) -> str:
    """
    Pretty print a trace.
    """
    return "\n".join(
        [
            pcode.pretty_insn(ctx.disassemble(addr))
            if isinstance(addr, int)
            else str(addr)
            for addr in trace
        ]
    )


@dataclass
class TraceState:
    start: StartStmt
    trace: Trace  # list of addresses
    state: pcode.SimState
    trace_id: list[int]
    ghost_env: dict[str, smt.ExprRef]  # = dataclasses.field(default_factory=dict)


def substitute_ghost(e: smt.ExprRef, ghost_env: dict[str, smt.ExprRef]) -> smt.ExprRef:
    """
    Substitute ghost variables in an expression.
    """
    return smt.substitute(
        e, *[(smt.Const(name, v.sort()), v) for name, v in ghost_env.items()]
    )


def substitute(
    e: smt.ExprRef,
    ctx: pcode.BinaryContext,
    memstate: pcode.MemState,
    ghost_env: dict[str, smt.ExprRef],
) -> smt.ExprRef:
    """
    Subsititute both ghost state and context (ram / registers). Usually you want this
    """
    return smt.simplify(
        ctx.substitute(memstate, smt.simplify(substitute_ghost(e, ghost_env)))
    )


class VerificationCondition(NamedTuple):
    """
    The result of symbolic execution over a path.
    There is a reason the execution started (entry point),
    the necessary conditions on the initial state to follow this path (path_cond),
    the memory state at the end of the path (memstate),
    the ghost environment at the end of the path (ghost_env),
    and the assertion that must hold at the end of the path (assertion).
    """

    start: StartStmt
    trace: list[int]
    path_cond: list[smt.BoolRef]
    memstate: pcode.MemState
    ghost_env: dict[str, smt.ExprRef]
    assertion: EndStmt
    # pf : Optional[kd.Proof] = None

    def __repr__(self):
        return f"VC({self.start},\n{[hex(addr) for addr in self.trace]},\n{self.assertion})"

    def vc(self, ctx: pcode.BinaryContext) -> smt.BoolRef:
        """
        Return the verification condition as an expression.
        """
        if isinstance(self.assertion, OutOfGas):
            return smt.BoolVal(False)
        return smt.Implies(
            smt.And(*self.path_cond),
            substitute(self.assertion.expr, ctx, self.memstate, self.ghost_env),
        )

    def verify(self, ctx: pcode.BinaryContext, **kwargs) -> kd.Proof:
        """
        Verify the verification condition using the given context.
        """
        vc1 = self.vc(ctx)
        vc = ctx.unfold(vc1)
        assert isinstance(vc, smt.BoolRef)
        try:
            return kd.prove(vc, **kwargs)
        except Exception as e:
            countermodel = e.args[2]
            if not isinstance(countermodel, smt.ModelRef):
                raise e
            raise Exception(
                "Verification failed for",
                self.assertion,
                self.countermodel(ctx, countermodel),
            )

    def countermodel(self, ctx: pcode.BinaryContext, m: smt.ModelRef) -> dict:
        """
        Interpret a countermodel on the relevant constants
        """
        # find all interesting selects
        interesting = {
            c
            for c in kd.utils.consts(self.start.expr)
            if not kd.utils.is_value(c) and not c.decl().name().startswith("ram")
        }
        if not isinstance(self.assertion, OutOfGas):
            interesting.update(
                c
                for c in kd.utils.consts(self.assertion.expr)
                if not kd.utils.is_value(c) and not c.decl().name().startswith("ram")
            )
            todo = [self.assertion.expr]
            while todo:
                t = todo.pop()
                if isinstance(t, smt.BoolRef):  # all boolean atoms
                    if t.decl().name() not in ["and", "or", "=>", "not"]:
                        interesting.add(t)
                if smt.is_select(t):
                    interesting.add(t)
                elif smt.is_app(t):
                    todo.extend(t.children())

        return {
            c: m.eval(substitute(c, ctx, self.memstate, self.ghost_env))
            for c in interesting
        }


def execute_spec_stmts(
    stmts: list[SpecStmt],
    tracestate: TraceState,
    ctx: pcode.BinaryContext,
    verbose=True,
) -> tuple[Optional[TraceState], list[VerificationCondition]]:
    """
    Execute a list of spec statements on a given trace state.
    """
    trace, state, ghost_env = tracestate.trace, tracestate.state, tracestate.ghost_env
    vcs = []
    for stmt in stmts:
        if verbose and not isinstance(stmt, Entry):
            print("Executing SpecStmt:", stmt)
        if isinstance(stmt, Entry):
            pass  # TODO: Tough to see if it should be nothing, assert or assume if you retouch entry point.
        elif isinstance(stmt, Assume):
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
                    start=tracestate.start,
                    trace=trace.copy(),
                    path_cond=state.path_cond.copy(),
                    memstate=state.memstate,
                    assertion=stmt,
                    ghost_env=ghost_env.copy(),
                )
            )
            if isinstance(stmt, Exit) or isinstance(stmt, Cut):
                # If this is an exit or cut, we end the execution of this path
                return None, vcs
        elif isinstance(stmt, Assign):
            # Assign a value to a variable in the ghost environment
            ghost_env = ghost_env.copy()
            ghost_env[stmt.name] = substitute(stmt.expr, ctx, state.memstate, ghost_env)
        else:
            raise Exception(
                f"Unexpected statement type {type(stmt)} in execute_specstmts"
            )
    return TraceState(
        start=tracestate.start,
        trace=trace,
        state=state,
        trace_id=tracestate.trace_id,
        ghost_env=ghost_env,
    ), vcs


def update_write(state, ghost_env):
    write = ghost_env["write"]
    for offset, size in state.memstate.write:
        for i in range(size // 8):
            write = smt.Store(write, smt.simplify(offset + i), True)
    state.memstate.write.clear()  #  TODO: This is really dirty
    res = {
        **ghost_env,
        "write": write,
    }
    return res


def execute_insn(
    tracestate: TraceState, ctx: pcode.BinaryContext, verbose=True
) -> list[TraceState]:
    """
    Execute one actual instruction from the current trace state.
    """
    # TODO : copy trace less. if single result
    state0 = tracestate.state
    addr, pc = state0.pc
    if pc != 0:
        raise Exception(f"Unexpected program counter {pc} at address {hex(addr)}")
    new_tracestates = ctx.sym_execute(
        state0.memstate,
        addr,
        path_cond=state0.path_cond,
        max_insns=1,
        verbose=verbose,
    )
    return [
        TraceState(
            start=tracestate.start,
            trace=tracestate.trace + [state0.pc[0]],
            state=state,
            trace_id=tracestate.trace_id
            if len(new_tracestates) == 1
            else tracestate.trace_id + [i],
            ghost_env=update_write(state, tracestate.ghost_env),
        )
        for i, state in enumerate(new_tracestates)
    ]


def execute_spec_and_insn(
    tracestate0: TraceState,
    spec: AsmSpec,
    ctx: pcode.BinaryContext,
    verbose=True,
) -> tuple[list[TraceState], list[VerificationCondition]]:
    """
    Execute spec statements and then one instruction.
    """
    addr = tracestate0.state.pc[0]
    specstmts = spec.addrmap.get(addr, [])
    tracestate, vcs = execute_spec_stmts(specstmts, tracestate0, ctx, verbose=verbose)
    if tracestate is None:
        return [], vcs
    new_tracestates = execute_insn(tracestate, ctx, verbose=verbose)
    return new_tracestates, vcs


def init_trace_states(
    ctx: pcode.BinaryContext, mem: pcode.MemState, spec: AsmSpec, verbose=True
) -> tuple[list[TraceState], list[VerificationCondition]]:
    """
    Initialize all trace states from the entry points in the spec.
    This will run the spec statements after the entry statement and also the first actual instruction.
    """
    todo = []
    vcs = []
    # Initialize executions out of entry points and cuts
    init_trace_id = -1
    for addr, specstmts in sorted(spec.addrmap.items(), key=lambda x: -x[0]):
        for n, stmt in enumerate(specstmts):
            if isinstance(stmt, Cut) or isinstance(stmt, Entry):
                init_trace_id += 1
                mem1 = mem.set_register(
                    ctx.pc[0], smt.BitVecVal(addr, ctx.pc[1] * 8)
                )  # set pc to start addr before entering code
                precond = ctx.substitute(mem1, stmt.expr)  # No ghost? Use substitute?
                ghost_env = {
                    "write": smt.K(smt.BitVecSort(mem1.bits), smt.BoolVal(False))
                    if isinstance(stmt, Entry)
                    else smt.Array("write", smt.BitVecSort(mem1.bits), smt.BoolSort())
                }
                assert isinstance(precond, smt.BoolRef)
                tracestate = TraceState(
                    start=stmt,
                    trace=[],
                    trace_id=[init_trace_id],
                    state=pcode.SimState(mem1, (addr, 0), [precond]),
                    ghost_env=ghost_env,
                )
                tracestate, new_vcs = execute_spec_stmts(
                    specstmts[n + 1 :], tracestate, ctx
                )
                vcs.extend(new_vcs)
                if tracestate is not None:
                    todo.extend(execute_insn(tracestate, ctx, verbose=verbose))
    return todo, vcs


def run_all_paths(
    ctx: pcode.BinaryContext, spec: AsmSpec, mem=None, verbose=True, max_insns=None
) -> list[VerificationCondition]:
    """
    Initialize queue with all stated entry points, and then symbolically execute all paths,
    collecting verification conditions (VCs) along the way.
    This interleaves executions of actual assembly instructions with spec statements.
    """
    if mem is None:
        mem = ctx.init_mem()  # pcode.MemState.Const("mem", bits=ctx.bits)
    todo, vcs = init_trace_states(ctx, mem, spec, verbose=verbose)
    # Execute pre specstmts and instructions
    while todo:
        tracestate = todo.pop()
        if verbose:
            print(
                "Continuing execution at:",
                hex(tracestate.state.pc[0]),
                "trace_id",
                tracestate.trace_id,
                "num insns",
                len(tracestate.trace),
            )
        if max_insns is not None and len(tracestate.trace) >= max_insns:
            vcs.append(
                VerificationCondition(
                    start=tracestate.start,
                    trace=tracestate.trace.copy(),
                    path_cond=tracestate.state.path_cond.copy(),
                    memstate=tracestate.state.memstate,
                    assertion=OutOfGas(),
                    ghost_env=tracestate.ghost_env.copy(),
                )
            )
            continue
        new_tracestates, new_vcs = execute_spec_and_insn(
            tracestate, spec, ctx, verbose=verbose
        )
        vcs.extend(new_vcs)
        todo.extend(new_tracestates)

        # addr = tracestate.state.pc[0]
        # specstmts = spec.addrmap.get(addr, [])
        # tracestate, new_vcs = execute_spec_stmts(specstmts, tracestate, ctx)
        # vcs.extend(new_vcs)
        # if tracestate is not None:
        #    todo.extend(execute_insn(tracestate, ctx, verbose=verbose))

    return vcs


class Debug:
    def __init__(
        self, ctx: pcode.BinaryContext, spec: Optional[AsmSpec] = None, verbose=True
    ):
        self.ctx = ctx
        if spec is None:
            self.spec = AsmSpec()
        else:
            self.spec: AsmSpec = spec
        self.tracestates: list[TraceState] = []
        self.vcs: list[VerificationCondition] = []
        self.breakpoints = set()
        self.verbose = verbose
        self._cur_model = None

    def spec_file(self, filename: str):
        self.spec = AsmSpec.of_file(filename, self.ctx)

    def label(self, label: str | int) -> int:
        assert self.ctx.loader is not None, (
            "BinaryContext must be loaded before disassembling"
        )
        if isinstance(label, str):
            sym = self.ctx.loader.find_symbol(label)
            if sym is None:
                raise Exception(
                    f"Symbol {label} not found in binary {self.ctx.filename}"
                )
            return sym.rebased_addr
        elif isinstance(label, int):
            return label
        else:
            raise Exception(f"Unexpected type {type(label)} for label")

    def add_entry(self, name, precond=smt.BoolVal(True)):
        self.spec.add_entry(name, self.label(name), precond)

    def add_exit(self, name, postcond=smt.BoolVal(True)):
        self.spec.add_exit(name, self.label(name), postcond)

    def add_cut(self, name, invariant):
        self.spec.add_cut(name, self.label(name), invariant)

    def add_assert(self, name, assertion):
        self.spec.add_assert(name, self.label(name), assertion)

    def add_assign(self, name, var_name, expr):
        self.spec.add_assign(name, self.label(name), var_name, expr)

    def start(self, mem=None):
        if mem is None:
            mem = self.ctx.init_mem()
        tracestates, vcs = init_trace_states(self.ctx, mem, self.spec)
        self.tracestates = tracestates
        self.vcs = vcs

    def breakpoint(self, addr):
        self.breakpoints.add(addr)

    def step(self, n=1):
        self._cur_model = None
        for _ in range(n):
            tracestate = self.pop()
            if self.verbose:
                print(
                    "Continuing execution at:",
                    hex(tracestate.state.pc[0]),
                    "trace_id",
                    tracestate.trace_id,
                    "num insns",
                    len(tracestate.trace),
                )
            new_tracestates, new_vcs = execute_spec_and_insn(
                tracestate, self.spec, self.ctx
            )
            self.vcs.extend(new_vcs)
            self.tracestates.extend(new_tracestates)

    def run(self):
        while self.tracestates:
            if self.addr() in self.breakpoints:
                break
            self.step()

    def run_vc(self):
        n = len(self.vcs)
        while len(self.vcs) == n:
            self.step()

    def pop_run(self):
        """
        Run until the current trace state is completely done.
        """
        n = len(self.tracestates)
        while len(self.tracestates) >= n:
            self.step()

    def pop_verify(self, **kwargs):
        vc = self.vcs.pop()
        vc.verify(self.ctx, **kwargs)

    def verify(self, **kwargs):
        if not self.vcs:
            raise Exception("No verification conditions to verify")
        if self.tracestates:
            raise Exception("There are still trace states to execute")
        while self.vcs:
            vc = self.vcs.pop(0)
            vc.verify(self.ctx)

    def pop_lemma(self) -> kd.tactics.ProofState:
        vc = self.vcs.pop()
        return kd.Lemma(vc.vc(self.ctx))

    def pop(self):
        return self.tracestates.pop()

    def addr(self):
        return self.tracestates[-1].state.pc[0]

    def ghost(self, name):
        return self.tracestates[-1].ghost_env[name]

    def reg(self, name):
        reg = self.ctx.state_vars[name]
        return smt.simplify(
            self.ctx.substitute(self.tracestates[-1].state.memstate, reg)
        )

    def ram(self, addr, size=None):
        """
        Get the expression held at at ram location addr
        """
        if size is None:
            size = self.ctx.bits // 8
        return smt.simplify(
            self.tracestates[-1].state.memstate.getvalue_ram(addr, size)
        )

    def insn(self):
        return self.ctx.disassemble(self.addr())

    def model(self):
        s = smt.Solver()
        s.add(self.tracestates[-1].state.path_cond)
        assert s.check() == smt.sat
        self._cur_model = s.model()

    def eval(self, expr: smt.ExprRef) -> smt.ExprRef:
        if self._cur_model is None:
            self.model()
        assert self._cur_model is not None
        tracestate = self.tracestates[-1]
        return smt.simplify(
            self._cur_model.eval(
                substitute(
                    expr, self.ctx, tracestate.state.memstate, tracestate.ghost_env
                )
            )
        )


@dataclass
class Results:
    successes: list[str] = dataclasses.field(default_factory=list)
    failures: list[str] = dataclasses.field(default_factory=list)


def assemble_and_gen_vcs(
    filename: str, langid="x86:LE:64:default", as_bin="as", max_insns=None
) -> tuple[pcode.BinaryContext, list[VerificationCondition]]:
    with open("/tmp/knuckle.s", "w") as f:
        f.write(kd_macro)
        f.flush()
    subprocess.run(
        [as_bin, filename, "-L", "-o", "/tmp/kdrag_temp.o"], check=True
    )  # -L to support local labels
    ctx = pcode.BinaryContext("/tmp/kdrag_temp.o", langid=langid)
    spec = AsmSpec.of_file(filename, ctx)
    return ctx, run_all_paths(ctx, spec, max_insns=max_insns)


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
