import click
from kdrag.contrib.pcode.asmspec import assemble_and_gen_vcs, pretty_trace, kd_macro
import sys
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
    "--timeout",
    default=1000,
    help="Timeout on verification conditions in milliseconds. Default is 1000ms.",
)
@click.option(
    "--max_insns",
    default=100000000,
    help="Maximum number of instructions to symbolically execute per path. Default is no limit.",
)
@click.option(
    "--print-macros",
    is_flag=True,
    help="Print annotation GAS macros. Give it a dummy filename",
)
def asmc(
    filename: str,
    langid: str,
    asm: str,
    print_macros: bool,
    timeout: int,
    max_insns: int,
):
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
    ctx, vcs = assemble_and_gen_vcs(
        filename, langid=langid, as_bin=asm, max_insns=max_insns
    )
    print("Checking verification conditions...")
    failures = 0
    for vc in reversed(vcs):
        try:
            vc.verify(ctx, timeout=timeout)
            print(f"[✅] {vc.assertion}")
        except TimeoutError:
            failures += 1
            print("")
            print("---------------------------------------------")
            print(f"[⏳] {vc.assertion} - Verification timed out.")
            print("Trace:")
            print(vc.start)
            print(pretty_trace(ctx, vc.trace))
            print(vc.assertion)
            print("---------------------------------------------")
            print("")
        except Exception as e:
            failures += 1
            print("")
            print("---------------------------------------------")
            print(f"[❌] {vc.assertion}")
            print("Trace:")
            print(vc.start)
            print(pretty_trace(ctx, vc.trace))
            print(vc.assertion)
            print("")
            print("Countermodel:")
            pprint.pp(e.args[2])
            print("---------------------------------------------")
            print("")
    if failures > 0:
        print(f"❌❌❌❌ {failures} verification conditions failed. ❌❌❌❌")
        sys.exit(1)
    else:
        print(f"✅✅✅✅ All {len(vcs)} verification conditions passed! ✅✅✅✅")
        sys.exit(0)


if __name__ == "__main__":
    asmc()
