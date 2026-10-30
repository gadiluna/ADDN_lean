#!/usr/bin/env python3
"""Require every formal statement and its entire checked dependency closure."""
import argparse
import copy
import json
from pathlib import Path
import subprocess
import tempfile

from check_claims import required_claim_ids, validate

ROOT = Path(__file__).resolve().parents[1]
SCOPE_FIELDS = {'schema_version', 'paper_title', 'completion_target', 'clause_coverage',
                'default_mode', 'registry_content', 'review_record', 'overrides'}


def required_claims(registry):
    return required_claim_ids({c['id']: c for c in registry['claims']})


def pending_obligations(profile, registry, all_records=False):
    """Identify any record without complete evidence; never accept scope overrides."""
    required = {c['id'] for c in registry['claims']} if all_records else required_claims(registry)
    overrides = profile.get('overrides', {})
    if not isinstance(overrides, dict):
        overrides = {}
    return sorted(c['id'] for c in registry['claims'] if c['id'] in required and
                  (c.get('status') != 'verified' or not c.get('lean_declarations') or c['id'] in overrides))


def completion_errors(profile, registry, all_records=False):
    missing = pending_obligations(profile, registry, all_records)
    if missing:
        return ['Complete proof evidence is required for every formal statement and supporting result: '
                + ', '.join(missing) + '.']
    return []


def validate_scope(profile, registry):
    if not isinstance(profile, dict):
        return ['Scope must be a JSON object.']
    errors = []
    if set(profile) != SCOPE_FIELDS:
        errors.append('Scope fields must describe only the complete current certification target.')
    checks = {
        'schema_version': 4,
        'paper_title': registry['paper']['title'],
        'completion_target': 'formal_statements',
        'clause_coverage': 'all',
        'default_mode': 'whole_verified_statement',
        'registry_content': 'formal_statements_and_required_dependencies',
        'review_record': 'docs/VALIDATION.md',
        'overrides': {},
    }
    for key, expected in checks.items():
        if profile.get(key) != expected:
            errors.append(f'Scope {key} must equal {expected!r}.')
    if not (ROOT / 'docs' / 'VALIDATION.md').is_file():
        errors.append('Current validation documentation is missing.')
    required = required_claims(registry)
    identifiers = {c['id'] for c in registry['claims']}
    if required != identifiers:
        errors.append('The registry must contain exactly the formal statements and their required dependency closure.')
    errors += completion_errors(profile, registry, all_records=True)
    return errors


def selected_declarations(profile, registry):
    """Return actual evidence for the required, wholly verified records."""
    required = required_claims(registry)
    overrides = profile.get('overrides', {})
    if not isinstance(overrides, dict):
        return set()
    return {name for claim in registry['claims'] if claim.get('status') == 'verified'
            and claim['id'] in required and claim['id'] not in overrides
            for name in claim.get('lean_declarations', [])}


def scope_self_test(profile, registry):
    errors, cases = [], []
    for key, value in [
        ('schema_version', 3), ('paper_title', 'A different article'),
        ('completion_target', 'subset'), ('clause_coverage', 'correctness_only'),
        ('default_mode', 'assume_verified'), ('registry_content', 'unrestricted'),
        ('review_record', 'absent.md'),
    ]:
        bad = copy.deepcopy(profile);bad[key] = value
        cases.append((key, bad, registry))
    formal = next(c for c in registry['claims'] if c['kind'] == 'numbered')
    support = next(c for c in registry['claims'] if c['kind'] != 'numbered')
    for record in (formal, support):
        bad = copy.deepcopy(profile)
        bad['overrides'][record['id']] = {'mode': 'outside_target'}
        cases.append(('override ' + record['id'], bad, registry))
    for record in (formal, support):
        bad = copy.deepcopy(registry)
        next(c for c in bad['claims'] if c['id'] == record['id'])['status'] = 'open'
        cases.append(('unverified ' + record['id'], profile, bad))
    bad = copy.deepcopy(registry)
    next(c for c in bad['claims'] if c['id'] == formal['id'])['lean_declarations'] = []
    cases.append(('absent actual evidence', profile, bad))
    bad = copy.deepcopy(registry)
    extra = copy.deepcopy(support);extra.update(id='unrelated-control', dependencies=[])
    bad['claims'].append(extra)
    cases.append(('unrelated inventory record', profile, bad))
    for name, candidate, data in cases:
        if not validate_scope(candidate, data):
            errors.append(f'Scope negative control failed: {name}.')
    if validate_scope(profile, registry):
        errors.append('Positive scope control rejected the complete current registry.')
    all_names = {n for c in registry['claims'] for n in c['lean_declarations']}
    if selected_declarations(profile, registry) != all_names:
        errors.append('Proof selection omitted required complete evidence.')
    bad = copy.deepcopy(registry)
    bad['claims'][0].update(status='open', lean_declarations=['Counting.UncheckedControl'])
    if 'Counting.UncheckedControl' in selected_declarations(profile, bad):
        errors.append('Unverified declaration was selected as checked evidence.')
    if not completion_errors(profile, bad):
        errors.append('Completion gate accepted an unverified required record.')
    return errors, len(cases)


def audit_declarations(names):
    source = 'import Counting.AllProofs\nimport Counting.AxiomAudit\n\n' + ''.join(
        f'#audit_declaration {name}\n' for name in sorted(names))
    with tempfile.NamedTemporaryFile(mode='w', suffix='.lean', dir=ROOT / '.lake',
                                     encoding='utf-8', delete=False) as handle:
        handle.write(source); temporary = Path(handle.name)
    try:
        subprocess.run(['lake', 'env', 'lean', str(temporary)], cwd=ROOT, check=True)
    finally:
        temporary.unlink()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--audit', action='store_true')
    parser.add_argument('--self-test', action='store_true')
    parser.add_argument('--require-complete', action='store_true', help='Full completion is also required by default.')
    parser.add_argument('--all-records', action='store_true', help='Every current record belongs to the required closure.')
    args = parser.parse_args()
    registry = json.loads((ROOT / 'claims.json').read_text(encoding='utf-8'))
    profile = json.loads((ROOT / 'scope.json').read_text(encoding='utf-8'))
    errors = validate(registry, (ROOT.parent / 'paper.tex').read_bytes(), require_complete=True)
    if not errors:
        errors += validate_scope(profile, registry)
    control_count = 0
    if args.self_test and not errors:
        controls, control_count = scope_self_test(profile, registry)
        errors += controls
    if errors:
        raise SystemExit('\n'.join(errors))
    names = selected_declarations(profile, registry)
    if args.audit:
        audit_declarations(names)
    formal_count = sum(c['kind'] == 'numbered' for c in registry['claims'])
    print(f'Complete formal scope validated: {formal_count} formal statements in '
          f'{len(registry["theorem_occurrences"])} occurrences; '
          f'{len(registry["claims"])-formal_count} required supporting records; '
          f'{len(names)} proved declaration endpoints.')
    if args.audit:
        print('All selected proof declarations passed the transitive axiom audit.')
    if args.self_test:
        print(f'{control_count} scope negative controls and four evidence/completion controls passed.')


if __name__ == '__main__':
    main()
