"""Render goal changes for directly edited theory proofs as PR Markdown."""

import argparse
import ast
from collections import Counter, defaultdict
from contextlib import redirect_stdout
from dataclasses import dataclass
from functools import cache
from importlib import import_module
from itertools import groupby
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

    selected = {(target.module, target.name): target for target in targets}
    steps = defaultdict(list)
    pending = {}

    def snapshot(state):
        # top_goal() can run callbacks, so read the stack directly.
        return tuple(
            goal._replace(sig=list(goal.sig), ctx=list(goal.ctx))
            for goal in reversed(state.goals)
            if isinstance(goal, tactics.Goal)
        )

    def profile(frame, event, _value):
        if event == "return" and frame in pending:
            target, label, line, source, before = pending.pop(frame)
            after = snapshot(frame.f_locals["self"])
            if tuple(map(goal_key, before)) != tuple(map(goal_key, after)):
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


def math_lines(value, width=COMMENT_WIDTH):
    # Some pretty-printer groups can still exceed the requested width.
    lines = []
    for line in value.splitlines():
        if len(line) <= width:
            lines.append(line)
            continue
        indent = line[: len(line) - len(line.lstrip())]
        lines.extend(
            wrap(
                line.lstrip(),
                width=width,
                initial_indent=indent,
                subsequent_indent=indent + "  ",
                break_long_words=False,
                break_on_hyphens=False,
            )
        )
    return lines


def math_block(value):
    return code("\n".join(math_lines(value)))


def goal_key(state):
    return (
        tuple(var.get_id() for var in state.sig),
        tuple(hyp.get_id() for hyp in state.ctx),
        state.goal.get_id(),
    )


def added_indices(before, after):
    remaining = Counter(term.get_id() for term in before)
    added = set()
    for index, term in enumerate(after):
        key = term.get_id()
        if remaining[key]:
            remaining[key] -= 1
        else:
            added.add(index)
    return added


def highlighted_goal(state, previous, *, removed=False):
    from kdrag.printers.pretty import pretty_goal

    width = COMMENT_WIDTH - 2  # Leave room for the diff prefix.
    text = pretty_goal(state, width=width)
    lines = text.splitlines()
    first_formula = next(
        (i for i, line in enumerate(lines) if re.match(r"^(?:\d+: |⊢ |─)", line)),
        None,
    )
    if first_formula is None:
        return "" if removed else math_block(text)

    new_locals = added_indices(previous.sig, state.sig)
    new_hypotheses = added_indices(previous.ctx, state.ctx)
    conclusion_changed = not previous.goal.eq(state.goal)
    # pretty_goal groups adjacent declarations of the same sort.
    local_marks = [
        any(i in new_locals for i, _ in group)
        for _, group in groupby(
            enumerate(state.sig), key=lambda item: item[1].sort().get_id()
        )
    ]
    if first_formula == len(state.sig) and first_formula != len(local_marks):
        # The pretty-printer's deep-expression fallback uses one line per local.
        local_marks = [i in new_locals for i in range(first_formula)]

    marked = False
    display = []
    if removed and new_locals:
        from kdrag.printers.pretty import _Printer, _sort

        printer = _Printer([*state.sig, *state.ctx, state.goal])
        for i in sorted(new_locals):
            var = state.sig[i]
            name = (
                var.sexpr()
                if printer.too_deep
                else printer.names.get(var.decl(), str(var))
            )
            decl = f"{name} : {_sort(var.sort())}"
            display.extend("- " + line for line in math_lines(decl, width))
    for i, line in enumerate(lines):
        if i < first_formula:
            if removed:
                continue  # A grouped declaration may include locals that survived.
            marked = i < len(local_marks) and local_marks[i]
        elif match := re.match(r"^(\d+): ", line):
            marked = int(match[1]) in new_hypotheses
            if removed:
                line = line[match.end() :]
        elif line.startswith("─"):
            marked = False
        elif line.startswith("⊢ "):
            marked = conclusion_changed
        if removed and not marked:
            continue
        prefix = ("- " if removed else "+ ") if marked else "  "
        display.extend(prefix + wrapped for wrapped in math_lines(line, width))
    return code("\n".join(display), "diff") if display else ""


def goals(states, before=()):
    from kdrag.printers.pretty import pretty_goal

    if not states:
        return "No open goals."
    existing = {goal_key(state): state for state in before}
    removal_only = len(before) == len(states) and all(
        old.goal.eq(state.goal)
        and not added_indices(old.sig, state.sig)
        and not added_indices(old.ctx, state.ctx)
        for old, state in zip(before, states)
    )
    rendered = []
    for number, state in enumerate(states, 1):
        if before:
            # A pending goal that becomes active is still the same goal.
            previous = existing.get(goal_key(state), before[0])
            block = highlighted_goal(state, previous)
        else:
            block = math_block(pretty_goal(state, width=COMMENT_WIDTH))
        if removal_only:
            removed = highlighted_goal(before[number - 1], state, removed=True)
            if removed:
                block += f"\n\n**Removed**\n\n{removed}"
        rendered.append(f"**Goal {number}**\n\n{block}")
    return "\n\n".join(rendered)


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
    for number, (tactic, line, source, before, after) in enumerate(steps, 1):
        snippet = code(source or tactic, "python")
        parts.append(
            f"<details>\n<summary>Step {number} · line {line}</summary>\n\n"
            f"{snippet}\n\n{goals(after, before)}\n\n</details>"
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
