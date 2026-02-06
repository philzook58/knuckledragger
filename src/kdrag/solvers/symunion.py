from dataclasses import dataclass
import kdrag.smt as smt
from typing import Callable


@dataclass(frozen=True)
class SymUnion[T]:
    values: tuple[tuple[smt.BoolRef, T], ...]

    @classmethod
    def wrap(cls, v: T) -> "SymUnion[T]":
        """
        Wrap a value in a SymUnion. This is monadic pure/return
        >>> SymUnion.wrap(42)
        SymUnion(values=((True, 42),))
        """
        return cls(((smt.BoolVal(True), v),))

    def map[U](self: "SymUnion[T]", f: Callable[[T], U]) -> "SymUnion[U]":
        return SymUnion(tuple((k, f(v)) for k, v in self.values))

    def map2[U, V](
        self: "SymUnion[T]", other: "SymUnion[U]", f: Callable[[T, U], V]
    ) -> "SymUnion[V]":
        """
        Map a binary function over two SymUnions

        """
        new_values = []
        for cond1, v1 in self.values:
            for cond2, v2 in other.values:
                new_values.append((smt.And(cond1, cond2), f(v1, v2)))
        return SymUnion(tuple(new_values))

    def flatmap[U](
        self: "SymUnion[T]", f: Callable[[T], "SymUnion[U]"]
    ) -> "SymUnion[U]":
        new_values = []
        for cond1, v1 in self.values:
            su2 = f(v1)
            for cond2, v2 in su2.values:
                new_values.append((smt.And(cond1, cond2), v2))
        return SymUnion(tuple(new_values))

    def join(self: "SymUnion[SymUnion[T]]") -> "SymUnion[T]":
        """
        Flatten a SymUnion of SymUnions. This is monadic join
        """
        new_values = []
        for cond1, su2 in self.values:
            for cond2, v2 in su2.values:
                new_values.append((smt.And(cond1, cond2), v2))
        return SymUnion(tuple(new_values))
