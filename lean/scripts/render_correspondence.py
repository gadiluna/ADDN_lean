#!/usr/bin/env python3
"""Render and validate the reader-facing paper-to-Lean correspondence map.

The registry supplies the inventory, manuscript identity and proof status.
correspondence_map.json selects the main proof endpoints.
Exact statements and printed numbers are read from the current manuscript.
Lean itself supplies each endpoint's qualified name, source module and line.
This tool does not replace the independent statement review or axiom audit.
"""
from __future__ import annotations

import argparse
import copy
import json
from pathlib import Path
import re
import subprocess
import tempfile

from check_claims import (DECLARATION, ENVIRONMENT, current_registry_view,
                          uncomment, validate as validate_registry)
from check_scope import pending_obligations, validate_scope

ROOT = Path(__file__).resolve().parents[1]
OUTPUT = ROOT / "docs/PAPER_LEAN_CORRESPONDENCE.md"
MAPPING = ROOT / "scripts/correspondence_map.json"


def validate_map(mapping: dict, registry: dict, profile: dict, paper: bytes) -> list[str]:
    errors = validate_registry(registry, paper)
    errors += validate_scope(profile, registry)
    formal = {c["id"]: c for c in registry["claims"] if c["kind"] == "numbered"}
    if len(formal) != 24 or len(registry["theorem_occurrences"]) != 26:
        errors.append("The reviewed inventory must have 24 statements and 26 occurrences.")
    if pending_obligations(profile, registry):
        errors.append("The correspondence document requires completed formal dependency closure.")
    if mapping.get("schema_version") != 1:
        errors.append("Unsupported correspondence map schema.")
    if set(mapping) != {"schema_version", "claims"}:
        errors.append("The correspondence map must contain only its schema and proof selections.")
    rows = mapping.get("claims", [])
    ids = [row.get("id") for row in rows]
    if len(ids) != len(set(ids)) or set(ids) != set(formal):
        errors.append("The map must contain every formal claim exactly once.")
    for row in rows:
        identifier = row.get("id")
        if identifier not in formal:
            continue
        claim = formal[identifier]
        if claim["status"] != "verified":
            errors.append(f"{identifier}: formal statement is not verified.")
        if set(row) != {"id", "proofs"}:
            errors.append(f"{identifier}: a proof selection must contain only id and proofs.")
        names = row.get("proofs", [])
        if not names or len(names) != len(set(names)):
            errors.append(f"{identifier}: proof endpoints must be nonempty and distinct.")
        for name in names:
            if not isinstance(name, str) or not DECLARATION.fullmatch(name):
                errors.append(f"{identifier}: invalid qualified Lean name {name!r}.")
            elif name not in claim["lean_declarations"]:
                errors.append(f"{identifier}: {name} is not registered evidence for this claim.")
    names = {name for row in rows for name in row.get("proofs", [])}
    if len(names) != 46:
        errors.append("The reviewed correspondence requires all 46 principal proof endpoints.")
    return errors


def lean_locations(names: list[str]) -> dict[str, tuple[Path, int]]:
    """Check actual theorem constants and ask Lean for their declaration ranges."""
    literals = ",\n    ".join("`" + name for name in names)
    source = """import Counting.AllProofs
import Lean
open Lean in
run_cmd do
  let names : Array Name := #[
    """ + literals + """]
  let env ← getEnv
  for n in names do
    match env.find? n with
    | some (.thmInfo _) => pure ()
    | _ => throwError "Correspondence endpoint is not a theorem: {n}"
    let some modIdx := env.getModuleIdxFor? n | throwError "No source module: {n}"
    let moduleName := env.header.moduleNames[modIdx]!
    let some ranges ← findDeclarationRanges? n | throwError "No source ranges: {n}"
    logInfo m!"CORRESPONDENCE\\t{n}\\t{moduleName}\\t{ranges.selectionRange.pos.line}"
"""
    with tempfile.NamedTemporaryFile(mode="w", suffix=".lean", prefix="correspondence-",
                                     dir=ROOT / ".lake", delete=False) as handle:
        handle.write(source)
        temporary = Path(handle.name)
    try:
        result = subprocess.run(["lake", "env", "lean", str(temporary)], cwd=ROOT,
                                text=True, capture_output=True, timeout=240)
    finally:
        temporary.unlink()
    if result.returncode:
        raise SystemExit("Lean endpoint/source lookup failed:\n" + result.stdout + result.stderr)
    locations = {}
    for line in result.stdout.splitlines():
        if not line.startswith("CORRESPONDENCE\t"):
            continue
        _, name, module, number = line.split("\t")
        if name in locations:
            raise SystemExit(f"Duplicate Lean location result: {name}")
        relative = Path(*module.split(".")).with_suffix(".lean")
        path, number = ROOT / relative, int(number)
        if not module.startswith("Counting.") or not path.is_file():
            raise SystemExit(f"Endpoint is not a project source file: {name}: {path}")
        lines = path.read_text().splitlines()
        short_name = re.escape(name.rsplit(".", 1)[1])
        declaration = rf"\b(?:theorem|lemma)\s+(?:[\w']+\.)*{short_name}(?=\s|[({{:]|$)"
        if not 1 <= number <= len(lines) or not re.search(declaration, lines[number - 1]):
            raise SystemExit(f"Lean metadata/source mismatch for {name}: {relative}:{number}; rebuild first.")
        locations[name] = (relative, number)
    if set(locations) != set(names):
        raise SystemExit("Lean did not return every requested declaration location.")
    return locations


def escape_cell(text: str) -> str:
    return text.replace("|", "&#124;").replace("\n", " ")


def lean_link(name: str, locations: dict) -> str:
    path, line = locations[name]
    return f"[{name}](../{path.as_posix()}#L{line})"


def ordered_rows(mapping: dict, registry: dict) -> list[dict]:
    occurrences = registry["theorem_occurrences"]
    return sorted(mapping["claims"], key=lambda row: min(
        o["start_line"] for o in occurrences if o["claim_id"] == row["id"]))


def paper_references(paper: bytes) -> dict[str, str]:
    """Resolve the section/equation references used inside the formal statements.

    The manuscript uses independent section and equation counters. Starred
    sections do not advance the section counter; appendix sections use letters.
    Formal-environment numbering is supplied separately by check_claims.
    """
    source = uncomment(paper.decode("utf-8"))
    token = re.compile(
        r"\\(?P<appendix>appendix)\b|\\section(?P<star>\*)?\{|"
        r"\\(?P<edge>begin|end)\{equation\}|"
        r"\\setcounter\{(?P<counter>section|equation)\}\{(?P<value>\d+)\}|"
        r"\\label\{(?P<label>[^}]+)\}")
    section = equation = 0
    appendix = in_equation = False
    refs = {}
    for match in token.finditer(source):
        if match.group("appendix"):
            appendix, section = True, 0
        elif match.group("counter"):
            if match.group("counter") == "section":
                section = int(match.group("value"))
            else:
                equation = int(match.group("value"))
        elif match.group("edge"):
            in_equation = match.group("edge") == "begin"
            if in_equation:
                equation += 1
        elif match.group("label"):
            label = match.group("label")
            if label.startswith("eq:") and in_equation:
                refs[label] = f"({equation})"
            elif label.startswith("sec:"):
                number = chr(ord("A") + section - 1) if appendix else str(section)
                refs[label] = f"Section {number}"
        elif match.group("star") is None:
            section += 1
    return refs


MATH = re.compile(
    r"\\begin\{equation\}(?P<equation>.*?)\\end\{equation\}|"
    r"\\\[(?P<display>.*?)\\\]|\\\((?P<inline>.*?)\\\)|"
    r"(?<!\\)\$(?P<dollar>.*?)(?<!\\)\$", re.S)


def normalize_math(source: str) -> str:
    """Expand paper-local macros without changing the mathematical expression."""
    source = re.sub(r"\\label\{[^}]+\}", "", source)
    for macro, expansion in (("anon", r"\mathbf{a}"), ("cand", r"\mathbf{b}"),
                             ("agents", r"\mathsf{A}")):
        source = re.sub(r"\\" + macro + r"\b", lambda _: expansion, source)
    source = source.replace(r"\rm{poly}", r"\mathrm{poly}")
    # Use upright spectrum notation supported by the Markdown math renderer.
    source = source.replace(r"\operatorname{Spec}", r"\mathrm{Spec}")
    # The cases contain text-mode inline mathematics in the TeX manuscript.
    # Split it into adjacent math/text pieces for a portable Markdown renderer.
    source = re.sub(r"\\text\{if \\\((.*?)\\\) and \\\((.*?)\\\)\}",
                    lambda m: r"\text{if }" + m[1] + r"\text{ and }" + m[2], source)
    # Cardinality bars otherwise delimit Markdown table cells.
    bars = source.count("|")
    if bars % 2:
        raise ValueError("An unmatched cardinality bar needs an explicit rendering review.")
    for index in range(bars):
        source = source.replace("|", r"\lvert " if index % 2 == 0 else r"\rvert ", 1)
    return " ".join(source.split())


def statement_cell(occurrence: dict, refs: dict[str, str]) -> str:
    """Render every word and formula of an occurrence, not a paraphrase."""
    match = ENVIRONMENT.search(uncomment(occurrence["excerpt"]))
    if match is None:
        raise ValueError("A formal occurrence lacks its complete source environment.")
    tex = match.group(3)
    tex = tex.replace(r"\qed", "")
    tex = re.sub(r"\\(?:Cref|cref)\{([^}]+)\}",
                 lambda m: refs[m[1]], tex)
    tex = re.sub(r"\\textnormal\{\\textsc\{([^{}]+)\}\}", r"\1", tex)
    result, cursor = [], 0
    for formula in MATH.finditer(tex):
        prose = re.sub(r"\\label\{[^}]+\}", "", tex[cursor:formula.start()])
        result.append(re.sub(r"\s+", " ", prose.replace("~", " ")))
        source = next(value for value in formula.groupdict().values() if value is not None)
        math = normalize_math(source)
        display = formula.group("display") is not None or formula.group("equation") is not None
        if formula.group("equation") is not None:
            labels = re.findall(r"\\label\{([^}]+)\}", source)
            if len(labels) != 1 or labels[0] not in refs:
                raise ValueError("A numbered statement equation needs its current printed number.")
            math += r"\qquad\text{" + refs[labels[0]] + "}"
        if display:
            result.append("<br/> $`\\displaystyle " + math + "`$ <br/>")
        else:
            result.append("$`" + math + "`$")
        cursor = formula.end()
    tail = re.sub(r"\\label\{[^}]+\}", "", tex[cursor:])
    result.append(re.sub(r"\s+", " ", tail.replace("~", " ")))
    cell = "".join(result).strip()
    if re.search(r"\\(?:anon|cand|agents|Cref|cref|label|qed)\b", cell):
        raise ValueError("An unresolved paper-local macro remains in a statement cell.")
    if "|" in cell or "\n" in cell:
        raise ValueError("The rendered statement would split the Markdown table.")
    return cell


def render(mapping: dict, registry: dict, locations: dict, paper: bytes) -> str:
    formal = {c["id"]: c for c in registry["claims"] if c["kind"] == "numbered"}
    occurrences = registry["theorem_occurrences"]
    rows = ordered_rows(mapping, registry)
    refs = paper_references(paper)
    out = [
        "# Paper–Lean correspondence", "",
        "**All 24 distinct formal statements of the paper are proved in Lean, covering all 26 "
        "lemma, theorem, and corollary occurrences and every clause of those statements.** "
        "This includes local polynomial runtime, the exact termination bounds, and both "
        "coNP-completeness results.", "",
        "This document maps the printed statements to the principal checked theorem declarations. "
        "The table includes repeated occurrences and identifies clauses proved by separate endpoints. "
        "Each source link opens the statement or its Lean declaration; the complete types, assumptions, "
        "and proof terms can be inspected there.", "",
        f"Manuscript: **[{registry['paper']['title']}](../../paper.tex)** "
        "([PDF](../../paper.pdf)).", "",
        "Generated from [claims.json](../claims.json) and "
        "[correspondence_map.json](../scripts/correspondence_map.json) by "
        "[render_correspondence.py](../scripts/render_correspondence.py). "
        "Lean supplies the qualified declaration names, source modules, and source lines. "
        "The generator resolves current source locations and printed numbers, checks every complete "
        "formal statement against the registry, and verifies the registered proof evidence and "
        "every declaration link.", "",
        "## Reading conventions and assumptions", "",
        "The scope is every clause of every formal lemma/theorem/corollary, together with all "
        "necessary proof dependencies. Bibliographic comparisons and unnumbered observations are "
        "outside this statement-level certification. A Lean proof may establish a statement by a "
        "different argument from its prose proof.", "",
        "Notation and standing assumptions are those of each linked paper section. The statement "
        "column reproduces the paper's full prose and formulas. Paper-local mathematical macros "
        "are expanded, cross-references use their printed numbers, and decorative proof-end "
        "symbols and LaTeX labels are omitted.", "",
        "In Lean theorem names, `exhaustive` refers to the paper's term *full*: "
        "the visible level contains every node of the complete history-tree level. "
        "For example, Lemma 16 is linked to `Counting.HardnessVisible.first_level_exhaustive`.", "",
        "The common model uses finite directed multigraphs, permits parallel arcs and self-loops, "
        "requires strong connectivity in every round, and supplies each anonymous agent with the "
        "known number of leaders. Agents send their previous state and learn their outdegree after "
        "sending; halted agents are silent. The lower bound ranges over protocols correct for every "
        "admissible population at the fixed leader count.", "",
        "The runtime statements concern the verified finite-alphabet machine operating on "
        "binary-encoded local state, shared view DAGs, and compressed message multiplicities. "
        "They charge initialization and all live local transitions. The bound is polynomial in "
        "`n + bits(M) + 1`, where `M` bounds the number of physical arcs per round; the paper's "
        "assumption `M ≤ 2^(a·n^k)` for fixed `a, k` yields a polynomial in `n`. "
        "Each transition starts with the encoded message input already supplied: collecting raw "
        "packets or preparing that input tape is not an additional charged operation in this model.", "",
        "Complexity-class membership and reductions use total binary languages, verified polynomial "
        "machine time, and polynomial witness lengths. Malformed vistas have empty spectrum; invalid "
        "network encodings are negative instances of `SomeAgentKnows`. The required external "
        "complexity results are included in the checked dependency chain.", "",
        "## Complete correspondence table", "",
        "Every row is **proved in full**. The first column uses the paper's actual independent "
        "lemma, theorem, and corollary counters. The repeated Flat level and vista "
        "coNP-completeness statements retain both printed occurrences and their full wordings "
        "within shared claim rows.", "",
        "| Printed number and source | Exact paper statement | Principal Lean proof declarations |",
        "| --- | --- | --- |",
    ]
    for row in rows:
        identifier = row["id"]
        copies = [o for o in occurrences if o["claim_id"] == identifier]
        sources, statements = [], []
        for index, occurrence in enumerate(copies):
            number = occurrence["printed_label"]
            title = occurrence["title"] or formal[identifier]["title"]
            title = title.replace(r"\(\mathsf{coNP}\)", "coNP")
            suffix = " (appendix repetition)" if len(copies) > 1 and index else ""
            sources.append(f"[{number}{suffix}](../../paper.tex#L{occurrence['start_line']})"
                           f"<br/>{escape_cell(title)}")
            statement = statement_cell(occurrence, refs)
            if len(copies) > 1:
                statement = f"**{number}{suffix}.** " + statement
            statements.append(statement)
        proofs = "<br/>".join(lean_link(name, locations) for name in row["proofs"])
        out.append(f"| {'<br/><br/>'.join(sources)} | {'<br/><br/>'.join(statements)} | {proofs} |")
    out += ["", "## Reproducing the verification", "",
            "The strict check rebuilds the proof aggregate, checks the registered declarations and "
            "their transitive dependencies, verifies current source coverage and exact formal statements, "
            "and runs the required semantic regression tests. The allowed logical axioms are "
            "`propext`, `Classical.choice`, and `Quot.sound`; the audit rejects `sorryAx`, added "
            "mathematical axioms, and native-evaluation axioms. See "
            "[VALIDATION.md](VALIDATION.md) for the verification procedure.", "",
            "From the `lean/` directory:", "",
            "```sh", "sh scripts/verify_semantic.sh",
            "python3 scripts/render_correspondence.py --check --self-test", "```", "",
            "The correspondence check requires every formal statement and its dependencies to be "
            "verified, includes every manuscript occurrence, and resolves all 46 principal "
            "proof declarations in Lean. It verifies the source module and declaration line "
            "for each link. Negative controls check that omissions, unregistered endpoints, "
            "unverified statements, and altered formal claims are rejected. Changes to unrelated "
            "prose are allowed; source links and printed numbers are resolved from the current paper.", "",
            "The [formal proof registry](FORMAL_CLAIMS.md) lists the supporting declarations; "
            "[CURRENT_SCOPE.md](CURRENT_SCOPE.md) defines the complete formal verification scope.", ""]
    return "\n".join(out)


def self_test(mapping: dict, registry: dict, profile: dict, paper: bytes) -> None:
    cases = []
    changed = copy.deepcopy(mapping)
    changed["claims"].pop()
    cases.append(("omitted formal claim", changed, registry, paper))
    changed = copy.deepcopy(mapping)
    changed["claims"].append(changed["claims"][0])
    cases.append(("duplicated formal claim", changed, registry, paper))
    changed = copy.deepcopy(mapping)
    changed["claims"][0]["proofs"] = ["Counting.NoSuchCorrespondenceTheorem"]
    cases.append(("unregistered endpoint", changed, registry, paper))
    changed = copy.deepcopy(mapping)
    changed["claims"][0]["proofs"] = []
    cases.append(("missing endpoint", changed, registry, paper))
    changed = copy.deepcopy(mapping)
    changed["claims"][0]["proofs"].append(changed["claims"][0]["proofs"][0])
    cases.append(("duplicated proof endpoint", changed, registry, paper))
    changed = copy.deepcopy(registry)
    next(c for c in changed["claims"] if c["kind"] == "numbered")["status"] = "conditional"
    cases.append(("unverified formal statement", mapping, changed, paper))
    changed = copy.deepcopy(registry)
    changed["theorem_occurrences"].pop()
    cases.append(("omitted occurrence", mapping, changed, paper))
    altered = paper.replace(b"uniquely determine the anonymities",
                            b"do not uniquely determine the anonymities", 1)
    if altered == paper:
        raise SystemExit("The formal-clause negative-control fixture needs review.")
    cases.append(("altered formal clause", mapping, registry, altered))
    for name, candidate, inventory, source in cases:
        if not validate_map(candidate, inventory, profile, source):
            raise SystemExit(f"Correspondence negative control failed: {name}")
    shifted = b"% Unrelated source-layout control.\n" + paper
    if validate_map(mapping, registry, profile, shifted):
        raise SystemExit("Correspondence positive control rejected unrelated source changes.")
    original = current_registry_view(registry, paper)["theorem_occurrences"]
    relocated = current_registry_view(registry, shifted)["theorem_occurrences"]
    for before, after in zip(original, relocated, strict=True):
        if (after["start_line"], after["end_line"], after["number"]) != (
                before["start_line"] + 1, before["end_line"] + 1, before["number"]):
            raise SystemExit("Current source locations did not follow an unrelated line shift.")
        if statement_cell(before, paper_references(paper)) != statement_cell(after, paper_references(shifted)):
            raise SystemExit("Statement rendering changed after an unrelated line shift.")
    print(f"Correspondence controls passed: {len(cases)} negative controls; unrelated prose/line shifts accepted.")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true", help="Reject a stale generated document.")
    parser.add_argument("--self-test", action="store_true", help="Run invalid-inventory negative controls.")
    args = parser.parse_args()
    registry_bytes = (ROOT / "claims.json").read_bytes()
    profile_bytes = (ROOT / "scope.json").read_bytes()
    mapping_bytes = MAPPING.read_bytes()
    registry, profile, mapping = map(json.loads, (registry_bytes, profile_bytes, mapping_bytes))
    paper_path = ROOT / registry["paper"]["path"]
    paper = paper_path.read_bytes()
    errors = validate_map(mapping, registry, profile, paper)
    if errors:
        raise SystemExit("Cannot render correspondence:\n" + "\n".join(errors))
    if args.self_test:
        self_test(mapping, registry, profile, paper)
    current = current_registry_view(registry, paper)
    names = sorted({name for row in mapping["claims"] for name in row["proofs"]})
    locations = lean_locations(names)
    content = render(mapping, current, locations, paper)
    if ((ROOT / "claims.json").read_bytes() != registry_bytes or
            (ROOT / "scope.json").read_bytes() != profile_bytes or
            MAPPING.read_bytes() != mapping_bytes or paper_path.read_bytes() != paper):
        raise SystemExit("Source changed during generation; rerun against a consistent snapshot.")
    if args.check:
        if not OUTPUT.is_file() or OUTPUT.read_text() != content:
            raise SystemExit("Stale correspondence document; run python3 scripts/render_correspondence.py")
    else:
        OUTPUT.write_text(content)
    print(f"Correspondence current: 24 formal claims, 26 occurrences, {len(names)} Lean theorem links.")


if __name__ == "__main__":
    main()
