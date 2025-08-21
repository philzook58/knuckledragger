import kdrag.smt as smt
import subprocess
import json
from dataclasses import dataclass, field
import kdrag as kd
import os


def call_yosys_functional(mod_name, verilog_filename):
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
