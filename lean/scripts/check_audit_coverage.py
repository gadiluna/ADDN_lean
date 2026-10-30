#!/usr/bin/env python3
"""Fail if a local theorem/lemma/axiom source is outside Audit's import closure.

Scan project source, excluding hidden/generated directories. This is a
conservative source guard, not a replacement for Lean: quoted
syntax containing declaration keywords may also be treated as proof-bearing.
Comments, string/character literals, and escaped identifiers are lexed first.
Read, lexical, and unresolved-local-import errors fail closed.
"""
from __future__ import annotations

import argparse
from dataclasses import dataclass
import json
import os
from pathlib import Path
import re
import tempfile

ROOT = Path(__file__).resolve().parents[1]


class CoverageError(Exception):
    pass


@dataclass(frozen=True)
class Token:
    value: str
    line: int
    identifier: bool = False
    escaped: bool = False


def tokens(source: str, filename: str) -> list[Token]:
    """Tokenize enough Lean to distinguish source keywords from prose/literals."""
    result: list[Token] = []
    i, line, n = 0, 1, len(source)
    while i < n:
        start, start_line = i, line
        if source[i].isspace():
            line += source[i] == "\n"
            i += 1
            continue
        if source.startswith("--", i):
            end = source.find("\n", i)
            i = n if end < 0 else end
            continue
        if source.startswith("/-", i):
            depth, i = 1, i + 2
            while i < n and depth:
                if source.startswith("/-", i):
                    depth, i = depth + 1, i + 2
                elif source.startswith("-/", i):
                    depth, i = depth - 1, i + 2
                else:
                    line += source[i] == "\n"
                    i += 1
            if depth:
                raise CoverageError(f"{filename}:{start_line}: unterminated block comment")
            continue
        raw = re.match(r'r(#+)?"', source[i:]) if source[i] == "r" else None
        if raw:
            close = '"' + (raw.group(1) or "")
            end = source.find(close, i + len(raw.group()))
            if end < 0:
                raise CoverageError(f"{filename}:{line}: unterminated raw string")
            i = end + len(close)
            line += source[start:i].count("\n")
            continue
        char = re.match(r"'(?:\\(?:u\{[0-9a-fA-F]+\}|x[0-9a-fA-F]{2}|.)|[^'\\\n])'",
                        source[i:]) if source[i] == "'" else None
        if char:
            i += len(char.group())
            continue
        if source[i] == '"':
            quote, i = source[i], i + 1
            while i < n:
                if source[i] == "\\":
                    i += 2
                elif source[i] == quote:
                    i += 1
                    break
                else:
                    i += 1
            else:
                raise CoverageError(f"{filename}:{line}: unterminated literal")
            line += source[start:i].count("\n")
            continue
        if source[i] == "«":
            end = source.find("»", i + 1)
            if end < 0:
                raise CoverageError(f"{filename}:{line}: unterminated escaped identifier")
            result.append(Token(source[i + 1:end], line, True, True))
            i = end + 1
            line += source[start:i].count("\n")
            continue
        if source[i].isalpha() or source[i] == "_":
            i += 1
            while i < n and (source[i].isalnum() or source[i] in "_'" or
                             "\u0300" <= source[i] <= "\u036f"):
                i += 1
            result.append(Token(source[start:i], line, True))
        else:
            result.append(Token(source[i], line))
            i += 1
    return result


def imports(items: list[Token], filename: str) -> list[str]:
    """Read the import header only; syntax quotations cannot manufacture edges."""
    result: list[str] = []
    i = 0
    while i < len(items):
        if items[i].value in {"module", "prelude"}:
            i += 1
            continue
        before = i
        while i < len(items) and items[i].value in {"public", "private", "meta"}:
            i += 1
        if i == len(items) or items[i].value != "import":
            break
        i += 1
        if i < len(items) and items[i].value == "all":
            i += 1
        if i == len(items) or not items[i].identifier:
            raise CoverageError(f"{filename}:{items[before].line}: import without a module")
        while True:
            parts = [items[i].value]
            last_line = items[i].line
            i += 1
            while i < len(items) and items[i].value == ".":
                i += 1
                if i == len(items) or not items[i].identifier:
                    raise CoverageError(f"{filename}:{last_line}: malformed module name")
                parts.append(items[i].value)
                last_line = items[i].line
                i += 1
            result.append(".".join(parts))
            if i == len(items) or items[i].line != last_line or not items[i].identifier:
                break
    return result


def sources(root: Path) -> dict[str, Path]:
    result: dict[str, Path] = {}

    def fail(error: OSError) -> None:
        raise error

    for directory, dirs, files in os.walk(root, onerror=fail):
        base = Path(directory)
        dirs[:] = sorted(d for d in dirs if not d.startswith(".") and d != "__pycache__")
        for name in dirs:
            if (base / name).is_symlink():
                raise CoverageError(f"Refusing an active source-directory symlink: {base / name}")
        for name in sorted(files):
            if not name.endswith(".lean") or name.startswith("."):
                continue
            path = base / name
            if path.is_symlink():
                raise CoverageError(f"Refusing a Lean source symlink: {path}")
            module = ".".join(path.relative_to(root).with_suffix("").parts)
            if module in result:
                raise CoverageError(f"Duplicate local module: {module}")
            result[module] = path
    return result


def check(root: Path) -> dict:
    local = sources(root)
    if "Audit" not in local:
        raise CoverageError("Missing local Audit.lean")
    prefixes = {name.split(".")[0] for name in local}
    graph: dict[str, list[str]] = {}
    proof_modules: dict[str, int] = {}
    for module, path in sorted(local.items()):
        items = tokens(path.read_text(encoding="utf-8"), str(path.relative_to(root)))
        graph[module] = []
        for dependency in imports(items, str(path.relative_to(root))):
            if dependency in local:
                graph[module].append(dependency)
            elif dependency.split(".")[0] in prefixes:
                raise CoverageError(f"{module}: unresolved local import {dependency}")
        declarations = sum(t.value in {"theorem", "lemma", "axiom"} and not t.escaped
                           for t in items)
        if declarations:
            proof_modules[module] = declarations
    closure: set[str] = set()
    pending = ["Audit"]
    while pending:
        module = pending.pop()
        if module not in closure:
            closure.add(module)
            pending.extend(graph[module])
    missing = sorted(set(proof_modules) - closure)
    if missing:
        raise CoverageError("Theorem/lemma/axiom modules outside Audit.lean's import closure:\n" +
                            "\n".join(f"  {m} ({proof_modules[m]} declaration keywords)" for m in missing))
    return {"root": "Audit", "local_modules": len(local),
            "audit_import_closure": len(closure), "proof_modules": len(proof_modules),
            "declaration_keywords": sum(proof_modules.values()), "uncovered_proof_modules": missing}


def self_test() -> int:
    with tempfile.TemporaryDirectory(prefix="lean-audit-coverage-") as temp:
        root = Path(temp)
        (root / "Audit.lean").write_text("import Main\n", encoding="utf-8")
        (root / "Main.lean").write_text("private theorem helper : True := by trivial\n", encoding="utf-8")
        noise = ('-- theorem imaginary axiom noise\n/- lemma nested /- theorem again -/ -/\n'
                 'def text := "escaped \\" theorem in a string"\n'
                 'def raw := r###"lemma in a raw string"###\n'
                 'def «theorem» := 1\n')
        (root / "Noise.lean").write_text(noise, encoding="utf-8")
        assert check(root)["proof_modules"] == 1
        assert [t.value for t in tokens("xs[i]'h; 'x'; '\\\"'", "fixture")
                if t.identifier] == ["xs", "i", "h"]

        def fails(fragment: str) -> None:
            try:
                check(root)
            except CoverageError as error:
                assert fragment in str(error), str(error)
            else:
                raise AssertionError(f"Expected failure containing {fragment!r}")

        (root / "ForgottenTests.lean").write_text("private lemma hidden : True := by trivial\n", encoding="utf-8")
        fails("ForgottenTests")
        (root / "Audit.lean").write_text('import Main\n-- import ForgottenTests\ndef t := "import ForgottenTests"\n', encoding="utf-8")
        fails("ForgottenTests")
        (root / "Audit.lean").write_text("import Main ForgottenTests\n", encoding="utf-8")
        assert check(root)["proof_modules"] == 2
        (root / "Untrusted.lean").write_text("axiom untrusted : False\n", encoding="utf-8")
        fails("Untrusted")
        (root / "Untrusted.lean").unlink()
        (root / "Audit.lean").write_text("import Main ForgottenTests\nimport Main.Missing\n", encoding="utf-8")
        fails("unresolved local import Main.Missing")
        (root / "Audit.lean").write_text("import Main ForgottenTests\n", encoding="utf-8")
        (root / "Noise.lean").write_text("/- unfinished", encoding="utf-8")
        fails("unterminated block comment")
        (root / "Noise.lean").write_text('def t := "unfinished', encoding="utf-8")
        fails("unterminated literal")
    return 9


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--self-test", action="store_true")
    parser.add_argument("--json", action="store_true", help="print machine-readable coverage counts")
    args = parser.parse_args()
    try:
        controls = self_test() if args.self_test else 0
        report = check(ROOT)
    except (CoverageError, OSError, UnicodeError, AssertionError) as error:
        print(f"Audit source coverage FAILED: {error}")
        return 1
    if args.json:
        print(json.dumps({**report, "self_tests": controls}, indent=2))
    else:
        print(f"Audit source coverage passed: {report['proof_modules']} theorem/lemma/axiom modules; "
              f"{report['audit_import_closure']}/{report['local_modules']} local modules imported; "
              f"{report['declaration_keywords']} declaration keywords; "
              f"{controls} self-tests passed.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
