"""
SSA is Functional Programming by Andrew Appel
https://www.cs.princeton.edu/~appel/papers/ssafun.pdf

Functional programming and SSA can be put into close correspondence.
It is to some degree a matter of pretty printing.

The recipe is to define one function per block that takes in all the currently live variables as arguments.
These are also called "block arguments" and are a structural alternative to phi nodes.

SSA variables are then just references given to previous expressions.
A maximal `let` bound form can be written. https://en.wikipedia.org/wiki/A-normal_form

Jumps are calls to the other function blocks

"""

from dataclasses import dataclass, field
import kdrag as kd
import kdrag.smt as smt
from collections import defaultdict


def pp_sort(s: smt.SortRef) -> str:
    if isinstance(s, smt.BitVecSortRef):
        return f"bv{s.size()}"
    else:
        return str(s)


@dataclass
class Block:
    sig: list[smt.SortRef]
    insns: list[smt.ExprRef]

    @classmethod
    def of_defined_fun(cls, f: smt.FuncDeclRef) -> "Block":
        """
        >>> x, y = smt.Ints("x y")
        >>> f = kd.define("f809", [x,y], x + x + y)
        >>> Block.of_defined_fun(f)
        ^(Int,Int):
        %0 = + %var0, %var0
        %1 = + %0, %var1
        """
        defn = kd.kernel.defns.get(f)
        if defn is None:
            raise ValueError(f"Function {f} is not defined to knuckledragger")
        else:
            body = defn._subst_fun_body
            return cls.of_expr(body, sig=[f.domain(i) for i in range(f.arity())])

    @classmethod
    def of_expr(cls, e: smt.ExprRef, sig=[]) -> "Block":
        """
        >>> x,y = smt.BitVecs("x y", 64)
        >>> x,y = smt.Var(1, smt.BitVecSort(64)), smt.Var(0, smt.BitVecSort(64))
        >>> z = smt.BitVec("z", 64)
        >>> Block.of_expr(smt.If(True, (x + y)*42, x - y + z), [smt.BitVecSort(64), smt.BitVecSort(64)])
        ^(bv64,bv64):
        %0 = bvadd %var1, %var0
        %1 = bvmul %0, 42
        %2 = bvsub %var1, %var0
        %3 = bvadd %2, z
        %4 = if True, %1, %3
        """
        if not smt.is_if(e):
            insns = []
            seen = set()
            todo = [e]
        else:
            insns = [e]
            seen = set(e.children())
            todo = list(e.children())
        while todo:
            e = todo.pop()
            # if smt.is_const(e) and not kd.utils.is_value(e):
            #    args.append(e)
            if smt.is_var(e):
                pass
            elif smt.is_const(e):
                continue
            else:
                insns.append(e)
                for arg in e.children():
                    if arg not in seen:
                        seen.add(arg)
                        todo.append(arg)
        insns.reverse()
        return cls(sig=sig, insns=insns)

    def vname(self, e: smt.ExprRef) -> str:
        # if any(e.eq(v) for v in self.args):
        #    return str(e)
        if smt.is_var(e):
            return f"%var{smt.get_var_index(e)}"
        elif smt.is_const(e):
            return str(e)
        else:
            for i, insn in enumerate(self.insns):
                if e.eq(insn):
                    return f"%{i}"
            else:
                raise ValueError(f"Value {e} not found in block")

    def __repr__(self) -> str:
        # res = [f"^({",".join(str(arg) for arg in self.args)})"]
        res = [f"^({','.join(pp_sort(s) for s in self.sig)}):"]
        for i, insn in enumerate(self.insns):
            if isinstance(insn, smt.BitVecRef) and smt.is_bv_value(insn):
                rhs = str(insn) + f":{insn.size()}"
            elif kd.utils.is_value(insn):
                rhs = str(insn)
            else:
                rhs = f"{insn.decl().name()} {", ".join(self.vname(arg) for arg in insn.children())}"
            res.append(f"\t%{i} = {rhs}")
        return "\n".join(res)

    def succ_calls(self) -> list[smt.ExprRef]:
        jmp = self.insns[-1]
        if smt.is_if(jmp):
            return jmp.children()
        else:
            return [jmp]


type Label = str


@dataclass
class Function:
    """ """

    entry: Label  # smt.FuncDeclRef?
    blocks: dict[Label, Block]  # 0th block is entry. Or "entry" is entry? Naw. 0th.

    @classmethod
    def of_defined_funs(cls, funs: list[smt.FuncDeclRef]):
        blocks = {f.name(): Block.of_defined_fun(f) for f in funs}
        entry = funs[0].name()
        return cls(entry=entry, blocks=blocks)

    def calls_of(self) -> dict[str, list[tuple[Label, smt.ExprRef]]]:
        """
        Returns a mapping from labels to a list of calls to that label
        """
        p = defaultdict(list)
        for label, blk in self.blocks.items():
            for call in blk.succ_calls():
                p[call.decl().name()].append((label, call))
        return p

    def phis(self):
        """
        Return the analog a mapping from labels to phi nodes in that block
        """

        preds = self.calls_of()
        phis = {}
        for label, blk in self.blocks.items():
            phis[label] = zip(*[call.children() for _, call in preds[label]])
        return phis

    def __repr__(self) -> str:
        res = [f"fn {self.entry} {{"]
        for label, blk in self.blocks.items():
            res.append(f"@{label}:")
            res.append(str(blk))
        res.append("}")
        return "\n".join(res)


@dataclass
class Spec:
    pre: dict[str, smt.BoolRef] = field(default_factory=dict)
    post: dict[str, smt.BoolRef] = field(default_factory=dict)
    cut: dict[str, smt.BoolRef] = field(default_factory=dict)


# def sym_exec():

Bottom = smt.DeclareSort("Bottom")
ret64 = smt.Function("ret64", smt.BitVecSort(64), Bottom)
