import re
import kdrag.smt as smt
import kdrag as kd
import dataclasses
import kdrag.contrib.pcode as pcode
from collections import defaultdict
import json
import subprocess

kd_macro = r"""
#precondition
.macro kd_entry label smt_expr
\label :
.endm

.macro kd_assert label smt_expr
\label :
.endm

.macro kd_assume label smt_expr
\label :
.endm

#postcondition
.macro kd_exit label smt_expr 
\label :
.endm

#invariant
.macro kd_cut label smt_expr
\label :
.endm 

.macro kd_always smt_expr
.endm
"""


# mapping from address to list of (label, expr)
type AddrMap = defaultdict[int, list[tuple[str, smt.BoolRef]]]


@dataclasses.dataclass
class AsmSpec:
    entries: AddrMap = dataclasses.field(default_factory=lambda: defaultdict(list))
    asserts: AddrMap = dataclasses.field(default_factory=lambda: defaultdict(list))
    assumes: AddrMap = dataclasses.field(default_factory=lambda: defaultdict(list))
    exits: AddrMap = dataclasses.field(default_factory=lambda: defaultdict(list))
    cuts: AddrMap = dataclasses.field(default_factory=lambda: defaultdict(list))

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
        decls = ctx._subst_decls.copy()
        decls["ram"] = smt.Array("ram", smt.BitVecSort(64), smt.BitVecSort(8))
        spec = cls()
        with open(filename) as f:
            for line in f.readlines():
                match = pattern.match(line)
                if match:
                    cmd, label, expr = match.groups()
                    assert ctx.loader is not None, (
                        "BinaryContext must be loaded before disassembling"
                    )
                    sym = ctx.loader.find_symbol(label)
                    if sym is None:
                        raise Exception(
                            f"Symbol {label} not found in binary {ctx.filename}"
                        )
                    else:
                        addr = sym.rebased_addr
                    expr = smt.parse_smt2_string(expr, decls=decls)[0]
                    if cmd == "kd_entry":
                        spec.entries[addr].append((label, expr))
                    elif cmd == "kd_assert":
                        spec.asserts[addr].append((label, expr))
                    elif cmd == "kd_assume":
                        spec.assumes[addr].append((label, expr))
                    elif cmd == "kd_exit":
                        spec.exits[addr].append((label, expr))
                    elif cmd == "kd_cut":
                        spec.cuts[addr].append((label, expr))
        return spec

    def __repr__(self):
        return json.dumps(
            dataclasses.asdict(self), indent=2, default=lambda b: b.sexpr()
        )


@dataclasses.dataclass
class Results:
    successes: list[str] = dataclasses.field(default_factory=list)
    failures: list[str] = dataclasses.field(default_factory=list)


def run_all_paths(ctx, spec: AsmSpec, mem=None, verbose=True) -> Results:
    if mem is None:
        mem = pcode.MemState.Const("mem")  # ctx.init_mem() very slow
    todo = []
    res = Results([], [])
    if len(spec.entries) == 0:
        raise Exception("No entry points found in the assembly specification")
    for addr, label_preconds in spec.entries.items():
        for label, precond in label_preconds:
            if verbose:
                print(f"entry {label} at {addr} with precond {precond}")
            todo.append(pcode.SimState(mem, (addr, 0), [ctx.substitute(mem, precond)]))

    def verif(state, prop):
        return kd.prove(
            smt.Implies(smt.And(*state.path_cond), ctx.substitute(state.memstate, prop))
        )

    while todo:
        state = todo.pop()
        addr, pc = state.pc
        if pc != 0:  # We don't support intra instruction assertions
            raise Exception(f"Unexpected program counter {pc} at address {hex(addr)}")
        if addr in spec.cuts:
            raise Exception("Cut not implemented yet")
        if addr in spec.asserts:
            for label, _assert in spec.asserts[addr]:
                try:
                    _pf = verif(state, _assert)
                    res.successes.append(f"[✅] assert {label}: {_assert}")
                except Exception as e:
                    res.failures.append(f"[❌] Error proving assert {label}: {_assert}")
                    print("[❌] Error proving assert", label, _assert, e)
                    # raise e
                # maybe prove form (state == current state => assert_expr)
        if addr in spec.exits:
            for label, _exit in spec.exits[addr]:
                try:
                    _pf = verif(state, _exit)
                    print(f"[✅] exit {label}: {_exit}")
                    res.successes.append(f"[✅] exit {label}: {_exit}")
                except Exception as e:
                    print("[❌] Error proving exit", label, _exit, e)
                    res.failures.append(f"[❌] Error proving exit {label}: {_exit}")
            continue  # Do not put back on todo
        if addr in spec.assumes:
            for label, _assume in spec.assumes[addr]:
                state._replace(
                    path_cond=state.path_cond
                    + [ctx.substitute(state.memstate, _assume)]
                )
        # Regular execution
        todo.extend(
            ctx.sym_execute(
                state.memstate,
                addr,
                path_cond=state.path_cond,
                max_insns=1,
                verbose=verbose,
            )
        )
    return res


def assemble_and_check(filename: str) -> Results:
    subprocess.run(["as", filename, "-o", "/tmp/kdrag_temp.o"], check=True)
    ctx = pcode.BinaryContext("/tmp/kdrag_temp.o")
    spec = AsmSpec.of_file(filename, ctx)
    print(spec)
    return run_all_paths(ctx, spec)


def assemble_and_check_str(asm_str: str) -> Results:
    with open("/tmp/kdrag_temp.s", "w") as f:
        f.write(asm_str)
        f.flush()
    return assemble_and_check("/tmp/kdrag_temp.s")
