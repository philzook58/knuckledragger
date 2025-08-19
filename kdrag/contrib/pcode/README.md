# ASMC - Assembly Checker

A tool to check verification conditions for assembly code using Ghidra PCode.

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

See blog post [A Python CLI for Verifying Assembly](https://www.philipzucker.com/asm_verify3/) for more.
