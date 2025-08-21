import kdrag.contrib.yosys as yosys
import kdrag.smt as smt
import kdrag as kd
import pytest

simple_or = """
module my_or(input my_in1, 
             input my_in2, 
             output my_out);
    assign my_out = my_in1 | my_in2;
endmodule
"""

def test_simple_or():
    with open("/tmp/simple_or.v", "w") as f:
        f.write(simple_or)
        f.flush()
    # run yosys
    #smt2 = yosys.functional_smt("my_or", "/tmp/simple_or.v")
    #vmod = yosys.reify_module("my_or", smt2)
    vmod = yosys.VerilogModule.from_file("my_or", "/tmp/simple_or.v")
    assert vmod.trans_fun.name() == "my_or"
    inputs = smt.Const("inputs", vmod.input_sort)
    state = smt.Const("state", vmod.state_sort)
    kd.prove(smt.ForAll([inputs, state], vmod.trans_fun(inputs, state).first.my_or_Outputs_my_out == inputs.my_or_Inputs_my_in1 | inputs.my_or_Inputs_my_in2),
             by=[vmod.trans_fun.defn])
    kd.prove(smt.ForAll([inputs, state], vmod.trans_fun(inputs, state).second == state),
             by=[vmod.trans_fun.defn])





counter = """
module counter (
    input  wire clk,
    output reg [3:0] count
);
    //initial counter = 0;
    always @(posedge clk)
        count <= count + 1;
endmodule
"""


def test_counter():
    with open("/tmp/counter.v", "w") as f:
        f.write(counter)
        f.flush()
    vmod = yosys.VerilogModule.from_file("counter", "/tmp/counter.v")
    assert vmod
    inputs = smt.Const("inputs", vmod.input_sort)
    state = smt.Const("counter-initial2", vmod.state_sort)
    outstate1 = vmod.trans_fun(inputs, state)
    state1 = outstate1.second
    out1 = outstate1.first
    outstate2 = vmod.trans_fun(inputs, state1)
    state2 = outstate2.second
    out2 = outstate2.first
    kd.prove(smt.ForAll([inputs,state],out2.counter_Outputs_count == out1.counter_Outputs_count + 1), 
                                                    by=[vmod.trans_fun.defn])

        
# https://yosyshq.readthedocs.io/projects/yosys/en/0.33/cmd/write_smt2.html
yosys_example = """
module test(input clk, output reg [3:0] y);
        always @(posedge clk)
        y <= (y << 1) | ^y;
endmodule
"""


def test_yosys_rel():
    # https://yosyshq.readthedocs.io/projects/yosys/en/0.33/cmd/write_smt2.html
    """
    ; declare two state variables s1 and s2
    (declare-fun s1 () test_s)
    (declare-fun s2 () test_s)

    ; state s2 is the successor of state s1
    (assert (test_t s1 s2))

    ; we are looking for a model with y non-zero in s1
    (assert (distinct (|test_n y| s1) #b0000))

    ; we are looking for a model with y zero in s2
    (assert (= (|test_n y| s2) #b0000))
    """
    with open("/tmp/test.v", "w") as f:
        f.write(yosys_example)
        f.flush()
    mod = yosys.VerilogModuleRel.from_file("test", ["y", "clk"], "/tmp/test.v")
    assert len(mod.wires) == 2
    s1,s2 = smt.Consts("s1 s2", mod.state_sort)
    kd.prove(kd.QForAll([s1,s2], mod.trans(s1,s2), mod.wires["y"](s1) != 0, mod.wires["y"](s2) != 0), unfold=1)
