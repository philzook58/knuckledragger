import click
from kdrag.contrib.pcode.asmspec import assemble_and_gen_vcs
import sys
import kdrag.smt as smt
import pprint
import kdrag.contrib.pcode as pcode


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
def asmc(filename: str, langid: str, asm: str):
    """Simple program that greets NAME for a total of COUNT times."""
    print(f"Processing {filename} with language ID {langid} using assembler {asm}")
    print("Constructing Trace Fragments...")
    ctx, vcs = assemble_and_gen_vcs(filename, langid=langid, as_bin=asm)
    print("Checking verification conditions...")
    fail = False
    for vc in vcs:
        try:
            vc.verify(ctx)
            print(f"[✅] {vc.cause}")
        except Exception as e:
            fail = True
            countermodel = e.args[2]
            if not isinstance(countermodel, smt.ModelRef):
                raise e
            print(f"[❌] {vc.cause}")
            print("---------------------------------------------")
            print("Trace:")
            print("\t", vc.start)
            for addr in vc.trace:
                print("\t", pcode.pretty_insn(ctx.disassemble(addr)))
            print("\t", vc.cause)
            print("")
            print("Countermodel:")
            pprint.pp(vc.countermodel(ctx, countermodel))

            print("---------------------------------------------")
    if fail:
        print("❌❌❌❌ Some verification conditions failed. ❌❌❌❌")
        sys.exit(1)
    else:
        print(f"✅✅✅✅ All {len(vcs)} verification conditions passed! ✅✅✅✅")
        sys.exit(0)


if __name__ == "__main__":
    asmc()
