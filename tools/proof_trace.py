"""Render goal changes for directly edited theory proofs as PR Markdown."""

import argparse
import ast
from collections import Counter, defaultdict
from contextlib import redirect_stdout
from dataclasses import dataclass
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


@cache
def standalone_comments(filename):
    source = "".join(linecache.getlines(filename))
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


def proof_arguments(node, value, proof_type):
    if isinstance(value, proof_type):
        yield node, value
    elif isinstance(node, (ast.List, ast.Tuple)) and isinstance(value, (list, tuple)):
        if len(node.elts) == len(value) and not any(
            isinstance(element, ast.Starred) for element in node.elts
        ):
            for element, item in zip(node.elts, value):
                yield from proof_arguments(element, item, proof_type)


def tactic_proofs(source, tactic, frame, proof_type):
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
    names = frame.f_code.co_varnames[1 : frame.f_code.co_argcount]
    for name, node in zip(names, call.args):
        if isinstance(node, ast.Starred):
            break
        yield from proof_arguments(node, frame.f_locals.get(name), proof_type)
    kwargs = frame.f_locals.get("kwargs", {})
    for keyword in call.keywords:
        if keyword.arg is not None:
            value = kwargs.get(keyword.arg, frame.f_locals.get(keyword.arg))
            yield from proof_arguments(keyword.value, value, proof_type)


def reference_value(node, caller):
    if isinstance(node, ast.Name):
        return caller.f_locals.get(node.id, caller.f_globals.get(node.id))
    if isinstance(node, ast.Attribute):
        owner = reference_value(node.value, caller)
        return getattr_static(owner, node.attr, None)
    return None


@cache
def binding_lines(filename):
    source = "".join(linecache.getlines(filename))
    bindings = {}
    for node in ast.parse(source, filename).body:
        if isinstance(node, ast.FunctionDef):
            bindings[node.name] = node.lineno
        elif isinstance(node, (ast.Assign, ast.AnnAssign)):
            names = node.targets if isinstance(node, ast.Assign) else [node.target]
            bindings.update(
                (name.id, node.lineno) for name in names if isinstance(name, ast.Name)
            )
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


def tactic_markup(source, tactic, frame, caller, revision, selected):
    from kdrag import Proof, pretty_expr

    annotations = {}
    for node, proof in tactic_proofs(source, tactic, frame, Proof):
        ref = node.func if isinstance(node, ast.Call) else node
        if (
            not isinstance(ref, (ast.Name, ast.Attribute))
            or ref.lineno != ref.end_lineno
        ):
            continue
        title = pretty_expr(proof.thm, width=COMMENT_WIDTH)
        url = lemma_link(ref, proof, caller, revision, selected)
        annotations[ref.lineno, ref.col_offset, ref.end_col_offset] = title, url
    if not annotations:
        return code(source, "python")

    lines = source.splitlines()
    for number, line in enumerate(lines, 1):
        utf8 = line.encode()
        cursor = 0
        chunks = []
        for (row, start, end), (title, url) in sorted(annotations.items()):
            if row != number or start < cursor:
                continue
            chunks.append(escape(utf8[cursor:start].decode()))
            label = escape(utf8[start:end].decode())
            title = escape(title, quote=True)
            if url:
                chunks.append(
                    f'<a href="{escape(url, quote=True)}" title="{title}">{label}</a>'
                )
            else:
                chunks.append(f'<span title="{title}">{label}</span>')
            cursor = end
        chunks.append(escape(utf8[cursor:].decode()))
        lines[number - 1] = "".join(chunks)
    return "<pre><code>" + "\n".join(lines) + "</code></pre>"


def record(targets, revision):
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
            target, line, snippet, before, comments = pending.pop(frame)
            after = snapshot(frame.f_locals["self"])
            if tuple(map(goal_key, before)) != tuple(map(goal_key, after)):
                steps[target].append((line, snippet, before, after, comments))
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
                    line,
                    tactic_markup(
                        source or tactic, tactic, frame, caller, revision, selected
                    ),
                    snapshot(state),
                    preceding_comments(caller.f_code.co_filename, line),
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


def trace_goal_text(state, width):
    from kdrag.printers.pretty import pretty_goal

    text = pretty_goal(state, width=width)
    if not (state.sig or state.ctx):
        return text
    lines = text.splitlines()
    for index, line in enumerate(lines):
        if line.startswith("⊢ "):
            if index and not lines[index - 1].startswith("─"):
                lines.insert(index, "─" * min(width, max(map(len, lines))))
            break
    return "\n".join(lines)


def highlighted_goal(state, previous):
    width = COMMENT_WIDTH - 2  # Leave room for the diff prefix.
    text = trace_goal_text(state, width)
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


def removed_indices(before, after):
    """Return deleted positions when after is a subsequence of before."""
    position = 0
    removed = set()
    for index, term in enumerate(before):
        if position < len(after) and term.eq(after[position]):
            position += 1
        else:
            removed.add(index)
    return removed if position == len(after) else None


def removal_plan(before, after):
    if len(before) != len(after):
        return None
    plan = []
    for old, new in zip(before, after):
        locals_removed = removed_indices(old.sig, new.sig)
        hypotheses_removed = removed_indices(old.ctx, new.ctx)
        if (
            not old.goal.eq(new.goal)
            or locals_removed is None
            or hypotheses_removed is None
        ):
            return None
        plan.append((locals_removed, hypotheses_removed))
    return plan


def goal_with_removals(state, previous, locals_removed, hypotheses_removed):
    from kdrag.printers.pretty import _Printer, _sort

    width = COMMENT_WIDTH - 2
    text = trace_goal_text(state, width)
    old_text = trace_goal_text(previous, width)
    boundary = re.compile(r"^(?:(\d+): |(?=[─⊢]))", re.M)
    old_boundaries = list(boundary.finditer(old_text))
    current_boundaries = list(boundary.finditer(text))
    separator_or_goal = next(
        (start for start in current_boundaries if start[1] is None), None
    )
    if not old_boundaries or separator_or_goal is None:
        return math_block(text)

    red_at = defaultdict(list)
    deleted = 0
    for index, (start, end) in enumerate(zip(old_boundaries, old_boundaries[1:])):
        if start[1] is None:
            break
        if index in hypotheses_removed:
            red_at[index - deleted].append(
                old_text[start.end() : end.start()].rstrip("\n")
            )
            deleted += 1

    display = []

    def append(value, prefix):
        display.extend(prefix + line for line in math_lines(value, width))

    first = current_boundaries[0].start()
    append(text[:first], "  ")
    if locals_removed:
        printer = _Printer([*previous.sig, *previous.ctx, previous.goal])
        for i in sorted(locals_removed):
            var = previous.sig[i]
            name = (
                var.sexpr()
                if printer.too_deep
                else printer.names.get(var.decl(), str(var))
            )
            append(f"{name} : {_sort(var.sort())}", "- ")

    for start, end in zip(current_boundaries, current_boundaries[1:]):
        if start[1] is None:
            break
        for former in red_at.pop(int(start[1]), []):
            append(former, "- ")
        append(text[start.start() : end.start()], "  ")
    for former in red_at.get(len(state.ctx), []):
        append(former, "- ")
    append(text[separator_or_goal.start() :], "  ")
    return code("\n".join(display), "diff")


def goals(states, before=()):
    if not states:
        return "No open goals."
    existing = {goal_key(state): state for state in before}
    removals = removal_plan(before, states)
    rendered = []
    for index, state in enumerate(states):
        if removals is not None and any(removals[index]):
            block = goal_with_removals(state, before[index], *removals[index])
        elif before:
            # A pending goal that becomes active is still the same goal.
            previous = existing.get(goal_key(state), before[0])
            block = highlighted_goal(state, previous)
        else:
            block = math_block(trace_goal_text(state, COMMENT_WIDTH))
        rendered.append(f"**Goal {index + 1}**\n\n{block}")
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

    parts.append("**Starting state**\n\n" + goals(steps[0][2]))
    shown_comments = set()
    for number, (line, snippet, before, after, comments) in enumerate(steps, 1):
        prose = ""
        if any(comments) and line not in shown_comments:
            prose = "<p>" + "<br>".join(map(escape, comments)) + "</p>\n\n"
            shown_comments.add(line)
        parts.append(
            f"{prose}<details>\n<summary>Step {number} · line {line}</summary>\n\n"
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
