import kdrag.smt as smt
import subprocess
import json
from dataclasses import dataclass, field
import kdrag as kd
import os
import shutil


def call_yosys_functional(mod_name, verilog_filename):
    # TODO: Maybe I need to do the /tmp/ shell game to avoid issues with yosys sandboxing
    directory, filename = os.path.split(verilog_filename)
    # clues about yosys processing for formal
    # https://github.com/YosysHQ/sby/blob/9675d158cea5b5289ef062297bff283788214a3b/sbysrc/sby_core.py#L1000
    yosys_command = f"""
    read_verilog -formal {filename};
    #hierarchy; 
    #proc; 
    #opt; 
    #memory -nordff -nomap; 
    #opt -fast;

    prep -top {mod_name};

    #clk2fflogic;
    
    
    async2sync;
    formalff -setundef -clk2ff -hierarchy; # -ff2anyinit not supported in functional smt?
    opt_clean;

    #dffunmap; 
    
    write_functional_smt2 functional_{mod_name}.smt2
    """
    subprocess.run(
        ["yowasp-yosys", "-p", yosys_command],
        cwd=directory,
        check=True,
        capture_output=True,
    )
    return open(os.path.join(directory, f"functional_{mod_name}.smt2"), "r").read()


def read_yosys_relational(filepath: str) -> str:
    filename = os.path.split(filepath)[-1]
    filepath1 = os.path.join("/tmp", filename)
    if filepath1 != filepath:
        shutil.copy(filepath, filepath1)
    outfile = "kdrag_verilog.smt2"
    yosys_command = f"read_verilog {filename}; \
        hierarchy -check; proc; opt; check -assert; \
        write_smt2 -bv {outfile}"
    res = subprocess.run(
        ["yowasp-yosys", "-p", yosys_command], cwd="/tmp", capture_output=True
    )
    if res.returncode != 0:
        raise Exception("Yosys error:", res.stderr.decode())

    return open(os.path.join("/tmp", outfile), "r").read()


@dataclass
class VerilogModule:
    """
    Data defining a functional model of a verilog module as a (input, state) -> (output, state) function.
    The fields of the inputs are `<module_name>_Inputs_<wire_name>`
    The output of the transition function is a pair`trans_fun(inputs,state).first` is the output Struct
    and `trans_fun(inputs,state).second` is the state Struct
    The fields of the outputs are `<module_name>_Outputs_<wire_name>`

    """

    input_sort: smt.SortRef
    output_sort: smt.SortRef
    state_sort: smt.SortRef
    init_constrs: list[smt.ExprRef]
    trans_fun: smt.FuncDeclRef

    @classmethod
    def from_file(cls, mod_name, verilog_filename):
        smt2 = call_yosys_functional(mod_name, verilog_filename)
        initial_constraints = smt.parse_smt2_string(smt2)
        module_semantics = smt.Function(
            "module_semantics", smt.BoolSort(), smt.BoolSort()
        )
        smt2 = (
            smt2
            + f"""(assert (module_semantics  
        (exists 
            ((inputs {mod_name}_Inputs) 
             (state {mod_name}_State)
             (out (Pair {mod_name}_Outputs {mod_name}_State))) 
            (= out ({mod_name} inputs state)))))"""
        )
        constrs = smt.parse_smt2_string(
            smt2, decls={"module_semantics": module_semantics}
        )
        assert len(constrs) == len(initial_constraints) + 1
        mod_sem = constrs[-1]
        assert smt.is_app(mod_sem) and mod_sem.decl() == module_semantics
        (inputs, state, outs), out_eq_body = kd.utils.open_binder_unhygienic(
            mod_sem.arg(0)
        )
        assert smt.is_eq(out_eq_body) and outs.eq(out_eq_body.arg(0))
        body = out_eq_body.arg(1)
        trans_fun = kd.define(mod_name, [inputs, state], body)
        return VerilogModule(
            input_sort=inputs.sort(),
            output_sort=outs.sort(),
            state_sort=state.sort(),
            init_constrs=initial_constraints,
            trans_fun=trans_fun,
        )


@dataclass
class VerilogModuleRel:
    """
    A relational model of a verilog module using yosys write_smt2 backend
    """

    name: str
    state_sort: smt.SortRef
    trans: smt.FuncDeclRef
    init: smt.FuncDeclRef
    init_unconstr: smt.FuncDeclRef
    asserts: smt.FuncDeclRef
    assumes: smt.FuncDeclRef
    wires: dict[str, smt.FuncDeclRef]

    @classmethod
    def from_file(cls, name: str, wire_names: list[str], filepath: str):
        # https://yosyshq.readthedocs.io/projects/yosys/en/0.33/cmd/write_smt2.html
        yosys_smt = read_yosys_relational(filepath)
        smtlib = [yosys_smt]

        state_sort = smt.DeclareSort(f"|{name}_s|")
        st, next_st = smt.Consts("state next_state", state_sort)

        # asserts can be read out by z3.parse_smt2_string. `define-fun` are automatically unfolded in the parser
        smtlib.append(f"""
        (declare-const state    |{name}_s|)
        (declare-const next_state |{name}_s|)
        """)
        smtlib.append(f"""
        (assert (|{name}_is| state))
        (assert (|{name}_i| state))
        (assert (|{name}_t| state next_state)) ; transition relation
        (assert (|{name}_a| state)) ; true if all assertions
        (assert (|{name}_u| state)) ; true is all assumptions
        """)
        for wire in wire_names:
            wire_name = f"|{name}_n {wire}|"
            # dummy equality. Easiest way
            smtlib.append(f"(assert (= ({wire_name} state) ({wire_name} state)))")
        smt_asserts = smt.parse_smt2_string("\n".join(smtlib))
        assert len(smt_asserts) == 5 + len(wire_names)
        init = kd.define(f"|{name}_is|", [st], smt_asserts[0])
        init_unconstr = kd.define(f"|{name}_i|", [st], smt_asserts[1])
        trans = kd.define(f"|{name}_t|", [st, next_st], smt_asserts[2])
        asserts = kd.define(f"|{name}_a|", [st], smt_asserts[3])
        assumes = kd.define(f"|{name}_u|", [st], smt_asserts[4])
        wires = {}

        for wire_name, expr in zip(wire_names, smt_asserts[5:]):
            assert smt.is_eq(expr)
            expr = expr.arg(0)
            wires[wire_name] = kd.define(f"|{name}_n {wire_name}|", [st], expr)
        return cls(
            name=name,
            state_sort=state_sort,
            init=init,
            init_unconstr=init_unconstr,
            trans=trans,
            asserts=asserts,
            assumes=assumes,
            wires=wires,
        )


@dataclass
class SmtModInfo:
    inputs: set = field(default_factory=set)
    outputs: set = field(default_factory=set)
    registers: set = field(default_factory=set)
    memories: dict = field(default_factory=dict)
    wires: set = field(default_factory=set)
    wsize: dict = field(default_factory=dict)
    clocks: dict = field(default_factory=dict)
    cells: dict = field(default_factory=dict)
    asserts: dict = field(default_factory=dict)
    assumes: dict = field(default_factory=dict)
    covers: dict = field(default_factory=dict)
    maximize: set = field(default_factory=set)
    minimize: set = field(default_factory=set)
    anyconsts: dict = field(default_factory=dict)
    anyseqs: dict = field(default_factory=dict)
    allconsts: dict = field(default_factory=dict)
    allseqs: dict = field(default_factory=dict)
    asize: dict = field(default_factory=dict)
    witness: list = field(default_factory=list)


def smt_metadata(filename):
    modinfo = dict()
    curmod = None
    topmod = None
    with open(filename) as f:
        for stmt in f.readlines():
            # extracted from
            # https://github.com/YosysHQ/yosys/blob/176131b50e349b401f11a21286385ae4006dbbca/backends/smt2/smtio.py#L534
            if not stmt.startswith("; yosys-smt2-"):
                continue

            fields = stmt.split()
            """
            if fields[1] == "yosys-smt2-solver-option":
                self.smt2_options[fields[2]] = fields[3]

            if fields[1] == "yosys-smt2-nomem":
                if self.logic is None:
                    self.logic_ax = False

            if fields[1] == "yosys-smt2-nobv":
                if self.logic is None:
                    self.logic_bv = False

            if fields[1] == "yosys-smt2-stdt":
                if self.logic is None:
                    self.logic_dt = True

            if fields[1] == "yosys-smt2-forall":
                if self.logic is None:
                    self.logic_qf = False
                self.forall = True
            """

            if fields[1] == "yosys-smt2-module":
                curmod = fields[2]
                modinfo[curmod] = SmtModInfo()

            if fields[1] == "yosys-smt2-cell":
                modinfo[curmod].cells[fields[3]] = fields[2]

            if fields[1] == "yosys-smt2-topmod":
                topmod = fields[2]

            if fields[1] == "yosys-smt2-input":
                modinfo[curmod].inputs.add(fields[2])
                modinfo[curmod].wsize[fields[2]] = int(fields[3])

            if fields[1] == "yosys-smt2-output":
                modinfo[curmod].outputs.add(fields[2])
                modinfo[curmod].wsize[fields[2]] = int(fields[3])

            if fields[1] == "yosys-smt2-register":
                modinfo[curmod].registers.add(fields[2])
                modinfo[curmod].wsize[fields[2]] = int(fields[3])

            if fields[1] == "yosys-smt2-memory":
                modinfo[curmod].memories[fields[2]] = (
                    int(fields[3]),
                    int(fields[4]),
                    int(fields[5]),
                    int(fields[6]),
                    fields[7] == "async",
                )

            if fields[1] == "yosys-smt2-wire":
                modinfo[curmod].wires.add(fields[2])
                modinfo[curmod].wsize[fields[2]] = int(fields[3])

            if fields[1] == "yosys-smt2-clock":
                for edge in fields[3:]:
                    if fields[2] not in modinfo[curmod].clocks:
                        modinfo[curmod].clocks[fields[2]] = edge
                    elif modinfo[curmod].clocks[fields[2]] != edge:
                        modinfo[curmod].clocks[fields[2]] = "event"

            if fields[1] == "yosys-smt2-assert":
                if len(fields) > 4:
                    modinfo[curmod].asserts["%s_a %s" % (curmod, fields[2])] = (
                        f"{fields[4]} ({fields[3]})"
                    )
                else:
                    modinfo[curmod].asserts["%s_a %s" % (curmod, fields[2])] = fields[3]

            if fields[1] == "yosys-smt2-cover":
                if len(fields) > 4:
                    modinfo[curmod].covers["%s_c %s" % (curmod, fields[2])] = (
                        f"{fields[4]} ({fields[3]})"
                    )
                else:
                    modinfo[curmod].covers["%s_c %s" % (curmod, fields[2])] = fields[3]

            if fields[1] == "yosys-smt2-assume":
                if len(fields) > 4:
                    modinfo[curmod].assumes["%s_u %s" % (curmod, fields[2])] = (
                        f"{fields[4]} ({fields[3]})"
                    )
                else:
                    modinfo[curmod].assumes["%s_u %s" % (curmod, fields[2])] = fields[3]

            if fields[1] == "yosys-smt2-maximize":
                modinfo[curmod].maximize.add(fields[2])

            if fields[1] == "yosys-smt2-minimize":
                modinfo[curmod].minimize.add(fields[2])

            if fields[1] == "yosys-smt2-anyconst":
                modinfo[curmod].anyconsts[fields[2]] = (
                    fields[4],
                    None if len(fields) <= 5 else fields[5],
                )
                modinfo[curmod].asize[fields[2]] = int(fields[3])

            if fields[1] == "yosys-smt2-anyseq":
                modinfo[curmod].anyseqs[fields[2]] = (
                    fields[4],
                    None if len(fields) <= 5 else fields[5],
                )
                modinfo[curmod].asize[fields[2]] = int(fields[3])

            if fields[1] == "yosys-smt2-allconst":
                modinfo[curmod].allconsts[fields[2]] = (
                    fields[4],
                    None if len(fields) <= 5 else fields[5],
                )
                modinfo[curmod].asize[fields[2]] = int(fields[3])

            if fields[1] == "yosys-smt2-allseq":
                modinfo[curmod].allseqs[fields[2]] = (
                    fields[4],
                    None if len(fields) <= 5 else fields[5],
                )
                modinfo[curmod].asize[fields[2]] = int(fields[3])

            if fields[1] == "yosys-smt2-witness":
                data = json.loads(stmt.split(None, 2)[2])
                if data.get("type") in [
                    "cell",
                    "mem",
                    "posedge",
                    "negedge",
                    "input",
                    "reg",
                    "init",
                    "seq",
                    "blackbox",
                ]:
                    modinfo[curmod].witness.append(data)

    return topmod, modinfo
