"""Render goal changes for directly edited theory proofs as PR Markdown."""

from __future__ import annotations

import argparse
import ast
from collections import Counter, defaultdict
from contextlib import redirect_stdout
from dataclasses import dataclass, replace
from functools import cache
from html import escape
from importlib import import_module
from inspect import getattr_static
from io import StringIO
from itertools import groupby
import linecache
from pathlib import Path
import re
import subprocess
import sys
from textwrap import dedent, wrap
import tokenize
from typing import TYPE_CHECKING

if TYPE_CHECKING:
    from kdrag import smt
    from kdrag.tactics import Goal


THEORIES = "src/kdrag/theories"
COMMENT_LIMIT = 55_000
COMMENT_WIDTH = 36
THEOREM_SEARCH = "https://www.philipzucker.com/knuckledragger/theorems.html"
REPOSITORY = "https://github.com/philzook58/knuckledragger"


@dataclass(frozen=True)
class Target:
    module: str
    name: str
    source: str | None = None


@dataclass(frozen=True)
class LemmaReference:
    line: int
    start: int
    end: int
    statement: smt.BoolRef
    url: str | None


@dataclass(frozen=True)
class Step:
    line: int
    source: str
    before: tuple[Goal, ...]
    after: tuple[Goal, ...] = ()
    comments: tuple[str, ...] = ()
    references: tuple[LemmaReference, ...] = ()


@cache
def source_tree(filename):
    source = "".join(linecache.getlines(filename))
    return source, ast.parse(source, filename)


def assignment_names(node):
    targets = node.targets if isinstance(node, ast.Assign) else [node.target]
    return [target.id for target in targets if isinstance(target, ast.Name)]


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
        source, tree = source_tree(str(path.resolve()))
        for node in tree.body:
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
                names = assignment_names(node)
                if len(names) != 1 or (
                    isinstance(node, ast.Assign) and len(node.targets) != 1
                ):
                    continue
                target = Target(module, names[0], ast.get_source_segment(source, node))
            else:
                continue
            if any(start <= node.end_lineno and end >= first for start, end in ranges):
                yield target


@cache
def source_statements(filename):
    source, tree = source_tree(filename)
    statements = [
        node
        for node in ast.walk(tree)
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


@cache
def standalone_comments(filename):
    source, _ = source_tree(filename)
    return {
        token.start[0]: (token.start[1], token.string[1:].strip())
        for token in tokenize.generate_tokens(StringIO(source).readline)
        if token.type == tokenize.COMMENT and not token.line[: token.start[1]].strip()
    }


def preceding_comments(filename, line):
    comments = standalone_comments(filename)
    source = linecache.getline(filename, line)
    indent = len(source) - len(source.lstrip())
    result = []
    while (comment := comments.get(line - 1)) is not None and comment[0] == indent:
        result.append(comment[1])
        line -= 1
    return list(reversed(result))


def tactic_proofs(source, tactic, frame, proof_type):
    parameter = {"apply": "pf", "rw": "rule", "exact": "pf"}.get(tactic)
    arguments = frame.f_locals
    support = arguments.get("kwargs", {}).get("by", arguments.get("by"))
    if support is None and parameter is None:
        return
    try:
        tree = ast.parse(source)
    except SyntaxError:
        return
    calls = [
        node
        for node in ast.walk(tree)
        if isinstance(node, ast.Call) and named(node, tactic)
    ]
    if len(calls) != 1:
        return

    call = calls[0]
    keywords = {keyword.arg: keyword.value for keyword in call.keywords}
    if parameter is not None and isinstance(
        proof := arguments.get(parameter), proof_type
    ):
        arg = call.args[0] if call.args else keywords.get(parameter)
        if arg is not None:
            yield arg, proof

    by = keywords.get("by")
    if by is None:
        return
    if isinstance(support, proof_type):
        yield by, support
    elif isinstance(by, (ast.List, ast.Tuple)) and isinstance(support, (list, tuple)):
        if len(by.elts) == len(support) and not any(
            isinstance(item, ast.Starred) for item in by.elts
        ):
            for node, proof in zip(by.elts, support):
                if isinstance(proof, proof_type):
                    yield node, proof


def reference_value(node, caller):
    if isinstance(node, ast.Name):
        return caller.f_locals.get(node.id, caller.f_globals.get(node.id))
    if isinstance(node, ast.Attribute):
        owner = reference_value(node.value, caller)
        return getattr_static(owner, node.attr, None)
    return None


@cache
def binding_lines(filename):
    _, tree = source_tree(filename)
    bindings = {}
    for node in tree.body:
        if isinstance(node, ast.FunctionDef):
            bindings[node.name] = node.lineno
        elif isinstance(node, (ast.Assign, ast.AnnAssign)):
            bindings.update((name, node.lineno) for name in assignment_names(node))
    return bindings


def lemma_link(node, proof, caller, revision, selected):
    definition = isinstance(node, ast.Attribute) and node.attr == "defn"
    value = reference_value(node.value if definition else node, caller)
    if value is None:
        value = proof if not definition else None
    if value is None:
        return None
    root = Path.cwd()
    for module_name, module in tuple(sys.modules.items()):
        if not module_name.startswith("kdrag.theories.") or module is None:
            continue
        filename = vars(module).get("__file__")
        if not filename:
            continue
        relative = Path(filename).resolve()
        if not relative.is_relative_to(root):
            continue
        for name, line in binding_lines(filename).items():
            if name.startswith("_") or vars(module).get(name) is not value:
                continue
            qualified = f"{module_name}.{name}"
            if (
                not definition
                and isinstance(value, type(proof))
                and (module_name, name) not in selected
                and qualified.isascii()
            ):
                anchor = re.sub(r"[^a-z0-9]+", "-", qualified.lower()).strip("-")
                return f"{THEOREM_SEARCH}#{anchor}"
            path = relative.relative_to(root).as_posix()
            return f"{REPOSITORY}/blob/{revision}/{path}#L{line}"
    return None


def lemma_references(source, tactic, frame, caller, revision, selected):
    from kdrag import Proof

    for node, proof in tactic_proofs(source, tactic, frame, Proof):
        ref = node.func if isinstance(node, ast.Call) else node
        if isinstance(ref, (ast.Name, ast.Attribute)) and ref.lineno == ref.end_lineno:
            yield LemmaReference(
                ref.lineno,
                ref.col_offset,
                ref.end_col_offset,
                proof.thm,
                lemma_link(ref, proof, caller, revision, selected),
            )


def record(targets, revision):
    from kdrag import Proof, tactics

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
        if event == "return":
            entry = pending.pop(frame, None)
            if entry is not None:
                target, step = entry
                after = snapshot(frame.f_locals["self"])
                if tuple(map(goal_key, step.before[:1])) != tuple(
                    map(goal_key, after[:1])
                ):
                    steps[target].append(replace(step, after=after))
            return
        if event != "call" or frame.f_globals is not vars(tactics):
            return

        caller = frame.f_back
        tactic = frame.f_code.co_name
        if caller is None or tactic.startswith("_"):
            return
        target = selected.get((caller.f_globals.get("__name__"), caller.f_code.co_name))
        state = frame.f_locals.get("self")
        if target is None or not isinstance(state, tactics.ProofState):
            return
        filename = caller.f_code.co_filename
        line, source = tactic_statement(filename, caller.f_lineno, tactic)
        source = source or tactic
        pending[frame] = (
            target,
            Step(
                line=line,
                source=source,
                before=snapshot(state),
                comments=tuple(preceding_comments(filename, line)),
                references=tuple(
                    lemma_references(source, tactic, frame, caller, revision, selected)
                ),
            ),
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
            yield target, proof.thm, steps[target]


def code(value, language="text"):
    fence = "`" * max([3, *(len(run) + 1 for run in re.findall(r"`+", value))])
    return f"{fence}{language}\n{value}\n{fence}"


def render_tactic(step):
    from kdrag import pretty_expr

    if not step.references:
        return code(step.source, "python")

    references = defaultdict(list)
    for ref in step.references:
        references[ref.line].append(ref)
    lines = []
    for number, line in enumerate(step.source.splitlines(), 1):
        # Python's AST columns count UTF-8 bytes.
        utf8 = line.encode()
        cursor = 0
        chunks = []
        for ref in sorted(references[number], key=lambda ref: ref.start):
            if ref.start < cursor:
                continue
            chunks.append(escape(utf8[cursor : ref.start].decode()))
            label = escape(utf8[ref.start : ref.end].decode())
            title = escape(pretty_expr(ref.statement, width=COMMENT_WIDTH), quote=True)
            if ref.url:
                chunks.append(
                    f'<a href="{escape(ref.url, quote=True)}" title="{title}">{label}</a>'
                )
            else:
                chunks.append(f'<span title="{title}">{label}</span>')
            cursor = ref.end
        chunks.append(escape(utf8[cursor:].decode()))
        lines.append("".join(chunks))
    return "<pre><code>" + "\n".join(lines) + "</code></pre>"


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


def highlighted_goal(state, previous):
    from kdrag.printers.pretty import pretty_goal

    width = COMMENT_WIDTH - 2  # Leave room for the diff prefix.
    text = pretty_goal(state, width=width)
    lines = text.splitlines()
    first_formula = next(
        (i for i, line in enumerate(lines) if re.match(r"^(?:\d+: |⊢ |─)", line)),
        None,
    )
    if first_formula is None:
        return math_block(text)

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
    for i, line in enumerate(lines):
        if i < first_formula:
            marked = i < len(local_marks) and local_marks[i]
        elif match := re.match(r"^(\d+): ", line):
            marked = int(match[1]) in new_hypotheses
        elif line.startswith("─"):
            marked = False
        elif line.startswith("⊢ "):
            marked = conclusion_changed
        prefix = "+ " if marked else "  "
        display.extend(prefix + wrapped for wrapped in math_lines(line, width))
    return code("\n".join(display), "diff")


def active_goal(states, before=()):
    from kdrag.printers.pretty import pretty_goal

    if not states:
        return "No open goals."
    state = states[0]
    if not before:
        return math_block(pretty_goal(state, width=COMMENT_WIDTH))
    # If a pending goal becomes active, its existing contents are unchanged.
    key = goal_key(state)
    previous = next((goal for goal in before if goal_key(goal) == key), before[0])
    return highlighted_goal(state, previous)


def render(target, statement, steps):
    from kdrag import pretty_expr

    name = f"{target.module}.{target.name}".removeprefix("kdrag.theories.")
    parts = [f"### `{name}`", math_block(pretty_expr(statement, width=COMMENT_WIDTH))]
    if not steps:
        if target.source:
            parts += [
                code(target.source, "python"),
                "This proof uses a single solver call.",
            ]
        else:
            parts += ["No direct goal-changing tactic calls were recorded."]
        return "\n\n".join(parts)

    parts.append("**Starting state**\n\n" + active_goal(steps[0].before))
    shown_comments = set()
    for number, step in enumerate(steps, 1):
        prose = ""
        if any(step.comments) and step.line not in shown_comments:
            prose = "<p>" + "<br>".join(map(escape, step.comments)) + "</p>\n\n"
            shown_comments.add(step.line)
        parts.append(
            f"{prose}<details>\n<summary>Step {number} · line {step.line}</summary>\n\n"
            f"{render_tactic(step)}\n\n{active_goal(step.after, step.before)}\n\n</details>"
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

    revision = subprocess.check_output(
        ["git", "rev-parse", args.head], text=True
    ).strip()
    parts = []
    size = 0
    for target, statement, steps in record(targets, revision):
        section = render(target, statement, steps)
        size += len(section.encode()) + 2
        if size > COMMENT_LIMIT:
            parts.append("Remaining proof traces exceed the comment size limit.")
            break
        parts.append(section)
    print("\n\n".join(parts))


if __name__ == "__main__":
    main()
