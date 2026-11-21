"""Render goal changes for directly edited theory proofs as PR Markdown."""

import argparse
import ast
from collections import defaultdict
from contextlib import redirect_stdout
from dataclasses import dataclass
from functools import cache
from importlib import import_module
import linecache
from pathlib import Path
import re
import subprocess
import sys
from textwrap import dedent, wrap


THEORIES = "src/kdrag/theories"
COMMENT_LIMIT = 55_000
COMMENT_WIDTH = 36


@dataclass(frozen=True)
class Target:
    module: str
    name: str
    source: str | None = None


def git_diff(*args):
    return subprocess.check_output(
        ["git", "diff", "--no-renames", *args], text=True, encoding="utf-8"
    )


def named(node, name):
    if isinstance(node, ast.Call):
        node = node.func
    return (isinstance(node, ast.Name) and node.id == name) or (
        isinstance(node, ast.Attribute) and node.attr == name
    )


def changed_targets(base, head):
    revs = f"{base}...{head}"
    files = git_diff("--diff-filter=AM", "--name-only", "-z", revs, "--", THEORIES)
    for filename in files.split("\0"):
        path = Path(filename)
        if path.suffix != ".py":
            continue
        patch = git_diff("--no-color", "--no-ext-diff", "-U0", revs, "--", filename)
        ranges = []
        for start, count in re.findall(r"^@@ .*? \+(\d+)(?:,(\d+))? @@", patch, re.M):
            first = int(start)
            length = int(count or "1")
            # For a deletion the hunk points to the preceding line in the head.
            ranges.append((first, first + (length - 1 if length else 1)))
        module = ".".join(path.relative_to("src").with_suffix("").parts)
        module = module.removesuffix(".__init__")
        source = path.read_text(encoding="utf-8")
        for node in ast.parse(source, filename).body:
            first = node.lineno
            if isinstance(node, ast.FunctionDef) and any(
                named(decorator, "Theorem") for decorator in node.decorator_list
            ):
                first = node.decorator_list[0].lineno
                target = Target(module, node.name)
            elif (
                isinstance(node, (ast.Assign, ast.AnnAssign))
                and isinstance(node.value, ast.Call)
                and named(node.value.func, "prove")
            ):
                names = node.targets if isinstance(node, ast.Assign) else [node.target]
                if len(names) != 1 or not isinstance(names[0], ast.Name):
                    continue
                target = Target(
                    module, names[0].id, ast.get_source_segment(source, node)
                )
            else:
                continue
            if any(start <= node.end_lineno and end >= first for start, end in ranges):
                yield target


@cache
def source_statements(filename):
    source = "".join(linecache.getlines(filename))
    statements = [
        node
        for node in ast.walk(ast.parse(source, filename))
        if isinstance(
            node, (ast.Expr, ast.Assign, ast.AnnAssign, ast.AugAssign, ast.Return)
        )
    ]
    return source, statements


def tactic_statement(filename, line, tactic):
    source, statements = source_statements(filename)
    statement = min(
        (
            node
            for node in statements
            if node.lineno <= line <= node.end_lineno
            and any(
                isinstance(call, ast.Call) and named(call, tactic)
                for call in ast.walk(node)
            )
        ),
        key=lambda node: (node.end_lineno - node.lineno, -node.col_offset),
        default=None,
    )
    if statement is not None:
        return statement.lineno, dedent(
            ast.get_source_segment(source, statement, padded=True)
        )
    return line, linecache.getline(filename, line).strip()


def record(targets):
    from kdrag import Proof, pretty_expr, tactics
    from kdrag.printers.pretty import pretty_goal

    selected = {(target.module, target.name): target for target in targets}
    steps = defaultdict(list)
    pending = {}

    def snapshot(state):
        # top_goal() can run callbacks, so read the stack directly.
        return tuple(
            pretty_goal(goal, width=COMMENT_WIDTH)
            for goal in reversed(state.goals)
            if isinstance(goal, tactics.Goal)
        )

    def profile(frame, event, _value):
        if event == "return" and frame in pending:
            target, label, line, source, before = pending.pop(frame)
            after = snapshot(frame.f_locals["self"])
            if before != after:
                steps[target].append((label, line, source, before, after))
        elif event == "call" and frame.f_globals is vars(tactics):
            caller = frame.f_back
            if caller is None or frame.f_code.co_name.startswith("_"):
                return
            target = selected.get(
                (caller.f_globals.get("__name__"), caller.f_code.co_name)
            )
            state = frame.f_locals.get("self")
            if target is not None and isinstance(state, tactics.ProofState):
                tactic = frame.f_code.co_name
                line, source = tactic_statement(
                    caller.f_code.co_filename, caller.f_lineno, tactic
                )
                pending[frame] = (
                    target,
                    tactic,
                    line,
                    source,
                    snapshot(state),
                )

    # Install the hook before importing any selected theory, including dependencies.
    previous = sys.getprofile()
    with redirect_stdout(sys.stderr):
        sys.setprofile(profile)
        try:
            modules = {name: import_module(name) for name, _ in selected}
        finally:
            sys.setprofile(previous)
    for target in targets:
        proof = getattr(modules[target.module], target.name, None)
        if isinstance(proof, Proof):
            yield target, pretty_expr(proof.thm, width=COMMENT_WIDTH), steps[target]


def code(value, language="text"):
    fence = "`" * max([3, *(len(run) + 1 for run in re.findall(r"`+", value))])
    return f"{fence}{language}\n{value}\n{fence}"


def math_block(value):
    # Some pretty-printer groups can still exceed the requested width.
    lines = []
    for line in value.splitlines():
        if len(line) <= COMMENT_WIDTH:
            lines.append(line)
            continue
        indent = line[: len(line) - len(line.lstrip())]
        lines.extend(
            wrap(
                line.lstrip(),
                width=COMMENT_WIDTH,
                initial_indent=indent,
                subsequent_indent=indent + "  ",
                break_long_words=False,
                break_on_hyphens=False,
            )
        )
    return code("\n".join(lines))


def goals(states):
    if not states:
        return "No open goals."
    return "\n\n".join(
        f"**Goal {number}**\n\n{math_block(state)}"
        for number, state in enumerate(states, 1)
    )


def render(target, statement, steps):
    name = f"{target.module}.{target.name}".removeprefix("kdrag.theories.")
    parts = [f"### `{name}`", math_block(statement)]
    if not steps:
        if target.source:
            parts += [
                code(target.source, "python"),
                "This proof uses a single solver call.",
            ]
        else:
            parts += ["No direct goal-changing tactic calls were recorded."]
        return "\n\n".join(parts)

    parts.append("**Starting state**\n\n" + goals(steps[0][3]))
    for number, (tactic, line, source, _, after) in enumerate(steps, 1):
        snippet = code(source or tactic, "python")
        parts.append(
            f"<details>\n<summary>Step {number} · line {line}</summary>\n\n"
            f"{snippet}\n\n{goals(after)}\n\n</details>"
        )
        if len("\n\n".join(parts).encode()) > COMMENT_LIMIT - 512:
            parts[-1] = "Remaining steps exceed the comment size limit."
            break
    return "\n\n".join(parts)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("base")
    parser.add_argument("head")
    parser.add_argument(
        "--list", action="store_true", help="list targets without importing proofs"
    )
    args = parser.parse_args()
    targets = list(changed_targets(args.base, args.head))
    if args.list:
        for target in targets:
            print(f"{target.module}.{target.name}")
        return

    parts = []
    size = 0
    for target, statement, steps in record(targets):
        section = render(target, statement, steps)
        size += len(section.encode()) + 2
        if size > COMMENT_LIMIT:
            parts.append("Remaining proof traces exceed the comment size limit.")
            break
        parts.append(section)
    print("\n\n".join(parts))


if __name__ == "__main__":
    main()
