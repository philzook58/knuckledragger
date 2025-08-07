import click
from kdrag.contrib.pcode.asmspec import assemble_and_gen_vcs, pretty_trace, kd_macro
import sys
import kdrag.smt as smt
import pprint


@click.command()
@click.argument("filename")
@click.option(
    "--langid",
    default="x86:LE:64:default",
    help="PCode language ID. Run `python3 -m pypcode --list` for options",
)
@click.option(
    "--asm",
    default="as",
    help="Assembler to use. Default is 'as'.",
)
@click.option(
    "--print-macros",
    is_flag=True,
    help="Print annotation GAS macros. Give it a dummy filename",
)
def asmc(filename: str, langid: str, asm: str, print_macros: bool):
    """
    asmc - Assembly Checker
    A tool to check verification conditions for assembly code using Ghidra PCode.

    Example:

    \b
    ```/tmp/test.s
    .include "/tmp/knuckle.s"
    .globl myfunc
    \b
    .text
        kd_entry myfunc "true"
        movq $42, %rax
        kd_exit .Lfunc_end "(= RAX (_ bv42 64))"
    ret
    ```
    \b
    ```
    python3 -m kdrag.contrib.pcode /tmp/test.s
    ```

    """
    if print_macros:
        print(kd_macro)  # TODO. This requires a filename still. Go to subcommands?
        sys.exit(0)
    print(f"Processing {filename} with language ID {langid} using assembler {asm}")
    print("Constructing Trace Fragments...")
    ctx, vcs = assemble_and_gen_vcs(filename, langid=langid, as_bin=asm)
    print("Checking verification conditions...")
    failures = 0
    for vc in vcs:
        try:
            vc.verify(ctx)
            print(f"[✅] {vc.cause}")
        except Exception as e:
            failures += 1
            countermodel = e.args[2]
            if not isinstance(countermodel, smt.ModelRef):
                raise e
            print(f"[❌] {vc.cause}")
            print("---------------------------------------------")
            print("Trace:")
            print(vc.start)
            print(pretty_trace(ctx, vc.trace))
            print(vc.cause)
            print("")
            print("Countermodel:")
            pprint.pp(vc.countermodel(ctx, countermodel))

            print("---------------------------------------------")
    if failures > 0:
        print(f"❌❌❌❌ {failures} verification conditions failed. ❌❌❌❌")
        sys.exit(1)
    else:
        print(f"✅✅✅✅ All {len(vcs)} verification conditions passed! ✅✅✅✅")
        sys.exit(0)


if __name__ == "__main__":
    asmc()
