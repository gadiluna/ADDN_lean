#!/usr/bin/env python3
"""Render the current formal proof registry and full-clause scope documents."""
import argparse
import json
from pathlib import Path

from check_claims import current_registry_view, validate
from check_scope import required_claims, selected_declarations, validate_scope

ROOT = Path(__file__).resolve().parents[1]


def render(data, profile):
    claims = data['claims']
    formal = [c for c in claims if c['kind'] == 'numbered']
    supporting = [c for c in claims if c['kind'] != 'numbered']
    declarations = selected_declarations(profile, data)
    count = len(data['theorem_occurrences'])
    identification = f"Paper: [{data['paper']['title']}](../../paper.tex) ([PDF](../../paper.pdf))."
    summary = f'**All {len(formal)} distinct formal statements are proved in full**, covering {count} lemma/theorem/corollary occurrences.'
    reader = ('The [paper–Lean correspondence](PAPER_LEAN_CORRESPONDENCE.md) provides the complete '
              'statement table and source links. [Validation](VALIDATION.md) explains the reproducible checks.')

    def occurrences(claim):
        return [o for o in data['theorem_occurrences'] if o['claim_id'] == claim['id']]

    def source_links(claim):
        links = ', '.join(f"[lines {s['start_line']}–{s['end_line']}](../../paper.tex#L{s['start_line']})" for s in claim['sources'])
        return links or claim.get('supporting_role', 'Supporting result; see the registered Lean declarations.')

    def esc(text):
        return text.replace('|', '\\|').replace('\n', ' ')

    formal.sort(key=lambda c: min(o['start_line'] for o in occurrences(c)))
    report = [
        '# Formal claims registry', '',
        'Generated from [claims.json](../claims.json) and [scope.json](../scope.json).', '',
        summary, '',
        'Every clause and every required supporting result is included, including polynomial local '
        'runtime and the complexity-class conclusions.', '', identification, '', reader, '',
        '## Complete statement coverage', '',
        '| Printed number(s) | Formal statement | All paper occurrences | Coverage |', '| --- | --- | --- | --- |',
    ]
    for claim in formal:
        links = ', '.join(f"[lines {o['start_line']}–{o['end_line']}](../../paper.tex#L{o['start_line']})" for o in occurrences(claim))
        labels = [o['printed_label'] for o in occurrences(claim)]
        numbers = ", ".join(dict.fromkeys(labels))
        if len(set(labels)) < len(labels):
            numbers += " (repeated)"
        report.append(f"| {numbers} | {claim['title']} (`{claim['id']}`) | {links} | Proved in full |")
    report += ['', '## Formal theorem evidence', '',
        'Every declaration below is checked by the registry proof audit. The correspondence table '
        'identifies the principal theorem endpoints with direct Lean source links. The exact '
        'formal statements and all supporting declarations are retained in the JSON registry.', '']
    for claim in formal:
        report += [f"### {claim['title']}", '', 'Source: ' + source_links(claim) + '.', '']
        report += [f'- `{name}`' for name in claim['lean_declarations']]
        report.append('')
    report += ['## Required supporting results', '',
        f'The formal statements require {len(supporting)} supporting registry records. Together the '
        f'{len(claims)} records cite {len(declarations)} distinct proved declarations. The checker '
        'requires exactly this transitive dependency closure: no required result may be omitted, '
        'and no unproved result may be accepted as evidence.', '',
        'Formal source links resolve the current exact statement. Supporting source links are optional '
        'contextual LaTeX labels; a supporting result without one identifies its role in the checked proof. The theorem names '
        'and dependency edges for every row are available in [claims.json](../claims.json).', '',
        '| Supporting result | Current source or proof role | Required predecessors |', '| --- | --- | --- |']
    for claim in supporting:
        deps = ', '.join(f'`{d}`' for d in claim['dependencies']) or '—'
        report.append(f"| `{claim['id']}` — {esc(claim['title'])} | {esc(source_links(claim))} | {deps} |")
    report += ['', '## Certification interface', '',
        'The target is every clause of every formal lemma, theorem and corollary and all proof '
        'dependencies required for those results. The proof may use a different argument from '
        'the prose proof. The [scope](CURRENT_SCOPE.md) specifies the model and runtime interface. '
        'The only permitted transitive axioms are `propext`, `Classical.choice` and `Quot.sound`.', '']

    scope = [
        '# Scope of the formalization', '', summary, '', identification, '',
        'The certification includes correctness, exact communication-round bounds, every stated '
        'graph restriction, encoded-size bounds, polynomial local computation, NP/coNP membership '
        'and both coNP-completeness results. All necessary external mathematical dependencies '
        'belong to the checked Lean proof closure.', '',
        '## Coverage', '', '| Item | Certified coverage |', '| --- | --- |',
        f'| Distinct formal statements | {len(formal)} |',
        f'| Formal occurrences, including repeats | {count} |',
        f'| Required supporting results | {len(supporting)} |',
        f'| Distinct registered proof declarations | {len(declarations)} |',
        '| Formal clauses | All |',
        '| Transitive axioms allowed | `propext`, `Classical.choice`, `Quot.sound` |', '', reader, '',
        '## Model and runtime interface', '',
        'The model uses finite anonymous agents in changing strongly connected directed multigraphs, '
        'with loops and parallel arcs allowed. Agents know the leader count, send their previous '
        'state and then learn their outdegree; halted agents are silent. Agent identities and '
        'the true population occur only in the network model and proofs.', '',
        'Local computation is measured in transitions of the verified finite-alphabet Turing machine. '
        'Each round receives encoded local state, binary-compressed messages and the learned '
        'outdegree. Initialization and every live local transition are charged. The general bound '
        'is polynomial in `n + bits(M) + 1`, where `M` bounds the total number of arcs in a round. '
        'The paper\'s `2^(poly(n))` arc bound makes total local time polynomial in `n`. '
        'Raw packet collection, physical communication and preparation of the external round input '
        'tape are outside this local input interface; native Lean, C and web execution times are '
        'not inferred from the finite-machine bound.', '',
        'Complexity-class results use total binary input languages, concrete polynomial-time '
        'verifiers and reductions, and proved witness bounds. Malformed vistas have empty '
        'spectrum. Invalid network encodings are negative instances of `SomeAgentKnows`.', '',
        '## Reproduce the certification', '', 'From `lean/`:', '', '```sh',
        'sh scripts/verify_semantic.sh', '```', '',
        'The command checks the source identification, exact source excerpts, complete formal '
        'coverage, dependency pins, source import coverage, aggregate compilation, transitive '
        'axioms, every registered declaration, all-clause scope and required regression suites. '
        'Registry labels alone are not proof evidence: the declaration audit imports the actual '
        'Lean declarations and checks their transitive assumptions.', '',
        'References use the paper title, stable LaTeX labels and complete formal statement text. '
        'Line links and printed numbers are resolved from the current source, including the repeated '
        'Lemma 1 counter reset. Unrelated prose edits and whitespace reflow do not invalidate the '
        'formal statement certificate. Changed mathematical statements require review. ', '',
        'This development targets the paper\'s formal statements and their required proof closure. '
        'Unnumbered observations and bibliographic comparisons are not independent certification '
        'obligations.', '',
    ]
    assert required_claims(data) == {c['id'] for c in claims}
    return {'docs/FORMAL_CLAIMS.md': report, 'docs/CURRENT_SCOPE.md': scope}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check', action='store_true')
    args = parser.parse_args()
    data = json.loads((ROOT / 'claims.json').read_text(encoding='utf-8'))
    profile = json.loads((ROOT / 'scope.json').read_text(encoding='utf-8'))
    errors = validate(data, (ROOT.parent / 'paper.tex').read_bytes(), require_complete=True)
    if not errors:
        errors += validate_scope(profile, data)
    if errors:
        raise SystemExit('Cannot render an invalid certification:\n' + '\n'.join(errors))
    current = current_registry_view(data, (ROOT.parent / 'paper.tex').read_bytes())
    for name, lines in render(current, profile).items():
        content = '\n'.join(lines).rstrip() + '\n'
        path = ROOT / name
        if args.check:
            if not path.exists() or path.read_text(encoding='utf-8') != content:
                raise SystemExit(f'Stale report: {name}; run python3 scripts/render_reports.py')
        else:
            path.write_text(content, encoding='utf-8')
    print('Formal registry and scope reports match the current certified source.')


if __name__ == '__main__':
    main()
