# ASMC - Assembly Checker

A tool to statically check verification conditions for assembly code using Ghidra PCode.

Install:

```bash
python3 -m pip install git+https://github.com/philzook58/knuckledragger.git[pypcode]
```

Example:

```as
.include "/tmp/knuckle.s"
.globl myfunc

.text
    kd_entry myfunc "true"
    movq $42, %rax
    kd_exit .Lfunc_end "(= RAX (_ bv42 64))"
ret
```

```bash
python3 -m kdrag.contrib.pcode /tmp/test.s
```

See blog post [A Python CLI for Verifying Assembly](https://www.philipzucker.com/asm_verify3/) for more information.

For more options:

```bash
python3 -m kdrag.contrib.pcode --help
```

# Known soundness issues and concerns

These are a mix of works in progress and won't fixes.

- I don’t think Ghidra semantics updates RIP explicitly
- MMIO and interrupts
- Interrupt throwing like div 0
- No modelling of memory permissions
- Concurrent code issues are unmodelled
- Alignment issues
- The code is concretely loaded at wherever cle says to
- Loaded code, bss, .data is not available.
- Dynamically generated or self modifying code is not modelled
- Syscalls
