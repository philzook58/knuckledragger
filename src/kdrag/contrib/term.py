from dataclasses import dataclass


@dataclass(frozen=True)
class Term:
    f: str
    args: tuple["Term", ...] = ()

    def __str__(self):
        if self.args:
            args_str = ", ".join(str(arg) for arg in self.args)
            return f"{self.f}({args_str})"
        else:
            return self.f


@dataclass(frozen=True)
class Var:
    name: str

    def __str__(self):
        return "?" + self.name


# pmatch

# unify
# LPO / KBO
# Tries


# class Bind / Lam
