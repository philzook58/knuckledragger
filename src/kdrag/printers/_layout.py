"""Shared document nodes and width-aware layout."""

from dataclasses import dataclass
from typing import cast


@dataclass(frozen=True)
class _Break:
    flat: str = " "


@dataclass(frozen=True)
class _Nest:
    doc: "_Doc"


@dataclass(frozen=True)
class _Group:
    doc: "_Doc"


type _Doc = str | tuple[_Doc, ...] | _Break | _Nest | _Group


def _layout(doc: _Doc, width: int) -> str:
    def fits(column: int, pending: list[tuple[int, bool, _Doc]]) -> bool:
        while pending and column <= width:
            indent, flat, part = pending.pop()
            if isinstance(part, str):
                column += len(part)
            elif isinstance(part, _Break):
                if not flat:
                    return True
                column += len(part.flat)
            elif isinstance(part, tuple):
                pending.extend(
                    (indent, flat, item)
                    for item in reversed(cast(tuple[_Doc, ...], part))
                )
            elif isinstance(part, _Nest):
                pending.append((indent + 2, flat, part.doc))
            elif isinstance(part, _Group):
                pending.append((indent, flat, part.doc))
            else:
                raise TypeError(f"Unexpected layout node: {type(part).__name__}")
        return column <= width

    pending = [(0, False, doc)]
    out = []
    column = 0
    while pending:
        indent, flat, part = pending.pop()
        if isinstance(part, str):
            out.append(part)
            column += len(part)
        elif isinstance(part, _Break):
            if flat:
                out.append(part.flat)
                column += len(part.flat)
            else:
                out.append("\n" + " " * indent)
                column = indent
        elif isinstance(part, tuple):
            pending.extend(
                (indent, flat, item) for item in reversed(cast(tuple[_Doc, ...], part))
            )
        elif isinstance(part, _Nest):
            pending.append((indent + 2, flat, part.doc))
        elif isinstance(part, _Group):
            flat = flat or fits(column, [*pending, (indent, True, part.doc)])
            pending.append((indent, flat, part.doc))
        else:
            raise TypeError(f"Unexpected layout node: {type(part).__name__}")
    return "".join(out)


def _join(sep: _Doc, parts: list[_Doc]) -> _Doc:
    result = []
    for part in parts:
        if result:
            result.append(sep)
        result.append(part)
    return tuple(result)
