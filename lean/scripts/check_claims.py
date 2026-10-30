#!/usr/bin/env python3
"""Check the current paper's complete formal-statement registry.

Source identity, exact statement coverage and dependency structure are checked
here. Lean compilation and transitive axiom auditing check the actual proofs.
"""
from __future__ import annotations

import argparse
import copy
import bisect
import json
from pathlib import Path
import re
import sys

ROOT = Path(__file__).resolve().parents[2]
KINDS = {'numbered', 'unnumbered', 'specification', 'implementation', 'external_dependency'}
DECLARATION = re.compile(r"[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*\Z")
ENVIRONMENT = re.compile(
    r'\\begin\{(lemma|theorem|corollary)\}(?:\[([^\]]*)\])?(.*?)\\end\{\1\}', re.S)
REGISTRY_FIELDS = {'schema_version', 'paper', 'scope', 'allowed_axioms', 'theorem_occurrences', 'claims'}
CLAIM_FIELDS = {'id', 'title', 'kind', 'area', 'status', 'statement', 'sources', 'dependencies',
                'lean_declarations', 'source_role', 'supporting_role'}


def uncomment(source: str) -> str:
    """Mask TeX comments without changing offsets or line numbers."""
    result = []
    for line in source.splitlines(keepends=True):
        for index, char in enumerate(line):
            if char != '%':
                continue
            backslashes, previous = 0, index - 1
            while previous >= 0 and line[previous] == '\\':
                backslashes += 1
                previous -= 1
            if backslashes % 2 == 0:
                line = line[:index] + ''.join('\n' if c == '\n' else ' ' for c in line[index:])
                break
        result.append(line)
    return ''.join(result)


def normalized_tex(text: str) -> str:
    """Ignore comments and whitespace reflow, preserving every nonspace token."""
    return ' '.join(uncomment(text).split())


def paper_title(source: str) -> str:
    matches = list(re.finditer(r'\\title\s*\{([^{}]*)\}', uncomment(source)))
    if len(matches) != 1:
        raise ValueError('Expected one plain-text manuscript title.')
    return normalized_tex(matches[0].group(1))


class SourceIndex:
    """Locate exact TeX excerpts after unrelated line shifts or whitespace reflow."""
    def __init__(self, source: str):
        self.source = source
        self.tokens = list(re.finditer(r'\S+', uncomment(source)))
        self.starts = []
        offset = 0
        for token in self.tokens:
            self.starts.append(offset)
            offset += len(token.group()) + 1
        self.text = ' '.join(token.group() for token in self.tokens)

    def resolve(self, excerpt: str) -> dict:
        if not isinstance(excerpt, str) or not normalized_tex(excerpt):
            raise ValueError('Source excerpt must be nonempty text.')
        needle = normalized_tex(excerpt)
        matches = []
        position = self.text.find(needle)
        while position >= 0:
            end = position + len(needle)
            if (position == 0 or self.text[position-1] == ' ') and (end == len(self.text) or self.text[end] == ' '):
                matches.append((position, end))
            position = self.text.find(needle, position+1)
        if len(matches) != 1:
            raise ValueError(f'Source excerpt must resolve uniquely in the current paper (found {len(matches)} matches).')
        start, end = matches[0]
        first = bisect.bisect_right(self.starts, start) - 1
        last = bisect.bisect_right(self.starts, end-1) - 1
        source_start = self.tokens[first].start() + start-self.starts[first]
        source_end = self.tokens[last].start() + end-self.starts[last]
        return {
            'start_line': self.source.count('\n', 0, source_start)+1,
            'end_line': self.source.count('\n', 0, source_end)+1,
            'excerpt': self.source[source_start:source_end],
        }


def environments(source: str) -> list[dict]:
    """Read current theorem headings and interpret the paper's actual counters.

    The supported numbering is independent Arabic lemma/theorem/corollary
    counters, integer set/add operations, and explicit saved-counter macros.
    Unsupported numbering changes fail instead of displaying guessed numbers.
    """
    clean = uncomment(source)
    types = {'lemma': 'Lemma', 'theorem': 'Theorem', 'corollary': 'Corollary'}
    for kind, heading in types.items():
        declarations = list(re.finditer(r'\\newtheorem\s*\{' + kind + r'\}', clean))
        expected = list(re.finditer(r'\\newtheorem\s*\{' + kind + r'\}\s*\{' + heading + r'\}(?!\s*\[)', clean))
        if len(declarations) != 1 or len(expected) != 1:
            raise ValueError(f'Unsupported declaration or shared/reset numbering for {kind}.')
    if re.search(r'\\(?:numberwithin|counterwithin|@addtoreset)\s*\{(?:lemma|theorem|corollary)\}', clean):
        raise ValueError('Unsupported formal-counter reset policy.')
    if re.search(r'\\(?:renewcommand|def|let)\*?\s*\{?\\the(?:lemma|theorem|corollary)\b', clean):
        raise ValueError('Unsupported formal-counter display redefinition.')
    formal = list(ENVIRONMENT.finditer(clean))
    starts = list(re.finditer(r'\\begin\{(?:lemma|theorem|corollary)\}', clean))
    if len(formal) != len(starts):
        raise ValueError('Malformed or unmatched formal statement environment.')
    events = [(m.start(), 'statement', m) for m in formal]
    saved_pattern = re.compile(r'\\edef\s*\\([A-Za-z@]+)\s*\{\s*\\number\s*\\value\s*\{(lemma|theorem|corollary)\}\s*\}')
    events += [(m.start(), 'save', m) for m in saved_pattern.finditer(clean)]
    operation_pattern = re.compile(r'\\(setcounter|addtocounter)\s*\{(lemma|theorem|corollary)\}\s*\{([^{}]*)\}')
    operations = list(operation_pattern.finditer(clean))
    operation_starts = list(re.finditer(r'\\(?:setcounter|addtocounter)\s*\{(?:lemma|theorem|corollary)\}', clean))
    if len(operations) != len(operation_starts):
        raise ValueError('Unsupported formal-counter assignment syntax.')
    events += [(m.start(), 'counter', m) for m in operations]
    counters = {kind: 0 for kind in types}
    saved, result = {}, []
    for _, event, match in sorted(events, key=lambda item: item[0]):
        if event == 'save':
            saved[match.group(1)] = counters[match.group(2)]
        elif event == 'counter':
            operation, kind, raw = match.groups()
            raw = raw.strip()
            if re.fullmatch(r'-?\d+', raw):
                value = int(raw)
            elif re.fullmatch(r'\\[A-Za-z@]+', raw) and raw[1:] in saved:
                value = saved[raw[1:]]
            else:
                raise ValueError(f'Unsupported or undefined formal-counter value: {raw!r}.')
            counters[kind] = value if operation == 'setcounter' else counters[kind]+value
        else:
            kind = match.group(1)
            counters[kind] += 1
            label = re.search(r'^\s*\\label\{([^}]+)\}', match.group(3))
            statement = re.sub(r'^\s*\\label\{[^}]*\}\s*', '', match.group(3)).strip()
            result.append({
                'occurrence': len(result)+1, 'environment': kind, 'title': match.group(2),
                'label': label.group(1) if label else None,
                'number': counters[kind], 'printed_label': f'{types[kind]} {counters[kind]}',
                'statement_tex': statement,
                'start_line': clean.count('\n', 0, match.start())+1,
                'end_line': clean.count('\n', 0, match.end())+1,
                'excerpt': source[match.start():match.end()],
            })
    return result


def current_occurrences(registry: dict, paper: bytes) -> list[dict]:
    """Resolve all registered occurrences by label/content and supply live numbering."""
    source = paper.decode('utf-8')
    if paper_title(source) != registry['paper'].get('title'):
        raise ValueError('Paper title does not match the registered manuscript.')
    recorded = registry.get('theorem_occurrences')
    if not isinstance(recorded, list):
        raise ValueError('theorem_occurrences must be a list.')
    fields = {'environment', 'title', 'label', 'claim_id', 'statement_tex'}
    for occurrence in recorded:
        if not isinstance(occurrence, dict) or set(occurrence) != fields:
            raise ValueError('Formal occurrence must contain its environment, title, label, owner and full statement.')
        if occurrence.get('environment') not in {'lemma', 'theorem', 'corollary'}:
            raise ValueError('Invalid formal occurrence environment.')
        if not isinstance(occurrence.get('claim_id'), str):
            raise ValueError('Invalid formal occurrence owner.')
        if not isinstance(occurrence.get('statement_tex'), str) or not occurrence['statement_tex'].strip():
            raise ValueError('Formal occurrence requires its entire statement text.')
    actual = environments(source)
    if len(recorded) != len(actual):
        raise ValueError(f'Theorem coverage mismatch: {len(recorded)} recorded, {len(actual)} in the paper.')
    used, result = set(), []
    for occurrence in actual:
        candidates = [i for i, ref in enumerate(recorded) if i not in used and
            ref['environment'] == occurrence['environment'] and ref['title'] == occurrence['title'] and
            ref['label'] == occurrence['label'] and
            (ref['label'] is not None or normalized_tex(ref['statement_tex']) == normalized_tex(occurrence['statement_tex']))]
        if len(candidates) != 1:
            raise ValueError('Formal statement does not have exactly one registered label/content match: '
                             + occurrence['printed_label'] + '.')
        index = candidates[0]
        expected = recorded[index]
        if normalized_tex(expected['statement_tex']) != normalized_tex(occurrence['statement_tex']):
            raise ValueError('Formal statement changed: ' + (occurrence['label'] or occurrence['printed_label']) + '.')
        used.add(index)
        result.append(dict(occurrence, claim_id=expected['claim_id']))
    return result


def current_registry_view(registry: dict, paper: bytes) -> dict:
    """Resolve live positions; optional contextual references do not pin prose."""
    result = copy.deepcopy(registry)
    source = paper.decode('utf-8')
    index = SourceIndex(source)
    result['theorem_occurrences'] = current_occurrences(registry, paper)
    for claim in result['claims']:
        if claim['kind'] == 'numbered':
            claim['sources'] = [index.resolve(ref['excerpt']) for ref in claim['sources']]
        else:
            refs = []
            for ref in claim['sources']:
                pattern = r'\\label\{' + re.escape(ref['context_label']) + r'\}'
                matches = list(re.finditer(pattern, uncomment(source)))
                if len(matches) == 1:
                    match = matches[0]
                    line = source.count('\n', 0, match.start())+1
                    refs.append({'start_line': line, 'end_line': line,
                                 'context_label': ref['context_label'], 'excerpt': source[match.start():match.end()]})
            claim['sources'] = refs
    return result


def required_claim_ids(claims: dict[str, dict]) -> set[str]:
    """Compute the formal roots' dependency closure, safely handling invalid edges."""
    work = [key for key, claim in claims.items() if claim.get('kind') == 'numbered']
    required = set()
    while work:
        identifier = work.pop()
        if identifier in required or identifier not in claims:
            continue
        required.add(identifier)
        dependencies = claims[identifier].get('dependencies', [])
        if isinstance(dependencies, list):
            work.extend(dep for dep in dependencies if isinstance(dep, str))
    return required


def validate(registry: object, paper: bytes, require_complete: bool = False) -> list[str]:
    errors = []
    if not isinstance(registry, dict):
        return ['Registry must be a JSON object.']
    if set(registry) != REGISTRY_FIELDS:
        errors.append('Registry fields must describe only the current source and proof closure.')
    if registry.get('schema_version') != 3:
        errors.append('Unsupported registry schema_version (expected 3).')
    if not isinstance(registry.get('scope'), str) or not registry['scope'].strip():
        errors.append('Scope description must be nonempty text.')
    try:
        source = paper.decode('utf-8')
    except UnicodeDecodeError:
        return errors + ['Paper must be UTF-8.']
    paper_meta = registry.get('paper', {})
    if not isinstance(paper_meta, dict):
        return errors + ['paper metadata must be an object.']
    if set(paper_meta) != {'path', 'title', 'theorem_environment_count', 'formal_statement_count'}:
        errors.append('Paper metadata must contain its title, path and formal statement counts.')
    if paper_meta.get('path') != '../paper.tex':
        errors.append('The registered paper path must be ../paper.tex.')
    try:
        if paper_title(source) != paper_meta.get('title'):
            errors.append('Paper title does not match the registered manuscript.')
    except ValueError as exc:
        errors.append(str(exc))
    source_index = SourceIndex(source)
    if registry.get('allowed_axioms') != ['propext', 'Classical.choice', 'Quot.sound']:
        errors.append('The declared axiom allowlist differs from the approved three axioms.')
    claims = registry.get('claims')
    if not isinstance(claims, list) or not claims:
        return errors + ['claims must be a nonempty list.']
    by_id = {}
    for claim in claims:
        if not isinstance(claim, dict):
            errors.append('Each claim must be an object.')
            continue
        identifier = claim.get('id')
        if not isinstance(identifier, str) or not re.fullmatch(r'[a-z][a-z0-9-]*', identifier):
            errors.append(f'Invalid claim id: {identifier!r}.')
            continue
        if identifier in by_id:
            errors.append(f'Duplicate claim id: {identifier}.')
        by_id[identifier] = claim

    def check_sources(owner, refs, formal):
        if not isinstance(refs, list) or (formal and not refs):
            errors.append(f"{owner}: sources must be a {'nonempty ' if formal else ''}list.")
            return
        for ref in refs:
            if formal:
                if not isinstance(ref, dict) or set(ref) != {'excerpt'}:
                    errors.append(f'{owner}: formal source references must contain their full TeX excerpt.')
                    continue
                try:
                    source_index.resolve(ref['excerpt'])
                except ValueError as exc:
                    errors.append(f'{owner}: {exc}')
            elif not isinstance(ref, dict) or set(ref) != {'context_label'} or not isinstance(ref['context_label'], str) or not ref['context_label'].strip():
                errors.append(f'{owner}: supporting source references must be optional contextual LaTeX labels.')

    for identifier, claim in by_id.items():
        if not set(claim) <= CLAIM_FIELDS:
            errors.append(f'{identifier}: unsupported claim fields.')
        for field in ('title', 'area', 'statement'):
            if not isinstance(claim.get(field), str) or not claim[field].strip():
                errors.append(f'{identifier}: {field} must be nonempty text.')
        if claim.get('status') != 'verified':
            errors.append(f'{identifier}: completion gate requires verified status.')
        if claim.get('kind') not in KINDS:
            errors.append(f"{identifier}: invalid kind {claim.get('kind')!r}.")
        role = claim.get('source_role')
        if role not in {'paper_claim', 'supporting_formalization', 'external_dependency'}:
            errors.append(f'{identifier}: source_role must identify a paper claim, supporting formalization or external dependency.')
        supporting = role in {'supporting_formalization', 'external_dependency'}
        if supporting:
            if claim.get('kind') == 'numbered':
                errors.append(f'{identifier}: a numbered claim cannot be supporting_formalization.')
            if (role == 'supporting_formalization' or not claim.get('sources')) and (not isinstance(claim.get('supporting_role'), str) or not claim['supporting_role'].strip()):
                errors.append(f'{identifier}: supporting formalization needs a precise supporting_role.')
        if role == 'external_dependency' and claim.get('kind') != 'external_dependency':
            errors.append(f'{identifier}: external_dependency source role requires the matching kind.')
        elif not supporting and 'supporting_role' in claim:
            errors.append(f'{identifier}: supporting_role requires supporting_formalization.')
        check_sources(identifier, claim.get('sources'), claim.get('kind') == 'numbered')
        declared = claim.get('lean_declarations')
        if not isinstance(declared, list) or any(
            not isinstance(name, str) or not DECLARATION.fullmatch(name) for name in declared
        ):
            errors.append(f'{identifier}: lean_declarations must be qualified declaration names.')
        elif not declared:
            errors.append(f'{identifier}: verified status requires actual lean_declarations.')
        elif len(set(declared)) != len(declared):
            errors.append(f'{identifier}: duplicate Lean declaration name.')
        dependencies = claim.get('dependencies')
        if not isinstance(dependencies, list) or any(not isinstance(dep, str) for dep in dependencies):
            errors.append(f'{identifier}: dependencies must be a list of claim IDs.')
            continue
        if len(set(dependencies)) != len(dependencies):
            errors.append(f'{identifier}: duplicate dependency.')
        for dep in dependencies:
            if dep not in by_id:
                errors.append(f'{identifier}: unknown dependency {dep}.')
            elif by_id[dep].get('status') != 'verified':
                errors.append(f'{identifier}: verified claim has unverified dependency {dep}.')

    visiting, visited = set(), set()
    def visit(identifier, path):
        if identifier in visiting:
            errors.append('Dependency cycle: ' + ' -> '.join(path + [identifier]))
            return
        if identifier in visited:
            return
        visiting.add(identifier)
        dependencies = by_id[identifier].get('dependencies', [])
        if isinstance(dependencies, list):
            for dep in dependencies:
                if isinstance(dep, str) and dep in by_id:
                    visit(dep, path + [identifier])
        visiting.remove(identifier)
        visited.add(identifier)
    for identifier in by_id:
        visit(identifier, [])
    unrelated = set(by_id) - required_claim_ids(by_id)
    if unrelated:
        errors.append('Registry contains records outside the formal proof closure: ' + ', '.join(sorted(unrelated)) + '.')

    try:
        current = current_occurrences(registry, paper)
    except ValueError as exc:
        return errors + [str(exc)]
    if paper_meta.get('theorem_environment_count') != len(current):
        errors.append('Theorem environment count mismatch.')
    owners = set()
    for occurrence in current:
        owner = occurrence['claim_id']
        if owner not in by_id:
            errors.append(f'Formal occurrence has unknown claim owner {owner!r}.')
            continue
        claim = by_id[owner]
        if claim.get('kind') != 'numbered':
            errors.append(f'{owner}: owning claim must have kind numbered.')
        refs = claim.get('sources', [])
        if not isinstance(refs, list) or not any(isinstance(ref, dict) and
                isinstance(ref.get('excerpt'), str) and normalized_tex(ref['excerpt']) == normalized_tex(occurrence['excerpt'])
                for ref in refs):
            errors.append(f'{owner}: formal occurrence lacks its full registered source excerpt.')
        if owner not in owners and normalized_tex(claim.get('statement', '')) != normalized_tex(occurrence['statement_tex']):
            errors.append(f'{owner}: formal statement must equal the complete first paper occurrence.')
        owners.add(owner)
    for identifier, claim in by_id.items():
        if claim.get('kind') == 'numbered' and identifier not in owners:
            errors.append(f'{identifier}: numbered claim has no theorem occurrence.')
    if paper_meta.get('formal_statement_count') != len(owners):
        errors.append('Distinct formal statement count mismatch.')
    return errors


def self_test(registry, paper):
    """Check formal-content guards and tolerance of unrelated editorial changes."""
    failures, cases = [], []
    def change(name, mutate, expected):
        candidate = copy.deepcopy(registry)
        mutate(candidate)
        cases.append((name, candidate, paper, expected))
    formal_index = next(i for i,c in enumerate(registry['claims']) if c['kind']=='numbered')
    change('paper title', lambda x:x['paper'].update(title='A different article'), 'Paper title does not match')
    change('formal excerpt', lambda x:x['claims'][formal_index]['sources'][0].update(excerpt='tampered'), 'Source excerpt must resolve uniquely')
    change('duplicate ID', lambda x:x['claims'].append(copy.deepcopy(x['claims'][0])), 'Duplicate claim id')
    change('unknown dependency', lambda x:x['claims'][0]['dependencies'].append('absent-obligation'), 'unknown dependency')
    change('cycle', lambda x:x['claims'][0]['dependencies'].append(x['claims'][0]['id']), 'Dependency cycle')
    change('missing occurrence', lambda x:x['theorem_occurrences'].pop(), 'Theorem coverage mismatch')
    change('missing proof evidence', lambda x:x['claims'][0].update(lean_declarations=[]), 'requires actual lean_declarations')
    change('unverified evidence', lambda x:x['claims'][0].update(status='open'), 'completion gate requires verified')
    change('changed allowlist', lambda x:x['allowed_axioms'].append('sorryAx'), 'axiom allowlist')
    change('count', lambda x:x['paper'].update(formal_statement_count=1), 'Distinct formal statement count')
    change('dropped registered clause', lambda x:x['claims'][formal_index].update(statement='Only correctness.'), 'complete first paper occurrence')
    change('bad declaration', lambda x:x['claims'][0].update(lean_declarations=['invalid; command']), 'qualified declaration names')
    change('extra field', lambda x:x.update(unchecked_certificate=True), 'only the current source and proof closure')
    change('invalid context reference', lambda x:x['claims'][0]['sources'][0].update(context_label=''), 'contextual LaTeX labels')
    change('duplicate evidence', lambda x:x['claims'][0]['lean_declarations'].append(x['claims'][0]['lean_declarations'][0]), 'duplicate Lean declaration')
    change('invalid occurrence owner', lambda x:x['theorem_occurrences'][0].update(claim_id='absent'), 'unknown claim owner')
    change('wrong source role', lambda x:x['claims'][0].update(source_role='unreviewed'), 'source_role must identify')
    def unrelated(x):
        helper=copy.deepcopy(x['claims'][0]);helper.update(id='unrelated-control',dependencies=[])
        x['claims'].append(helper)
    change('unrelated record', unrelated, 'outside the formal proof closure')
    helper_index=next(i for i,c in enumerate(registry['claims']) if c['source_role']=='supporting_formalization')
    change('missing support role', lambda x:x['claims'][helper_index].pop('supporting_role'), 'needs a precise supporting_role')
    change('numbered support', lambda x:x['claims'][formal_index].update(source_role='supporting_formalization',supporting_role='helper'), 'numbered claim cannot be supporting')
    change('sourceless formal claim', lambda x:x['claims'][formal_index].update(sources=[]), 'sources must be a nonempty list')
    source=paper.decode('utf-8')
    first=next(ENVIRONMENT.finditer(uncomment(source)))
    changed=source[:first.end(3)]+' This extra conclusion is not registered. '+source[first.end(3):]
    cases.append(('changed paper clause',registry,changed.encode(), 'Formal statement changed'))
    dropped=source[:first.start()]+source[first.end():]
    cases.append(('dropped paper statement',registry,dropped.encode(), 'Theorem coverage mismatch'))
    core=next(m for m in ENVIRONMENT.finditer(uncomment(source)) if m.group(2)=='Core algorithm')
    body=source[core.start(3):core.end(3)]
    if 'All local computations' not in body:
        failures.append('Runtime-clause negative control cannot locate its test clause.')
    else:
        shorter=source[:core.start(3)]+body.split('All local computations')[0]+source[core.end(3):]
        cases.append(('dropped paper runtime',registry,shorter.encode(),'Formal statement changed'))
    shared=source.replace(r'\newtheorem{theorem}{Theorem}',r'\newtheorem{theorem}[lemma]{Theorem}')
    cases.append(('unsupported shared counters',registry,shared.encode(),'Unsupported declaration'))
    for name,candidate,content,message in cases:
        if not any(message in error for error in validate(candidate,content,True)):
            failures.append(f'Negative control failed: {name}.')
    positive=[('current paper',paper),
              ('unrelated prose and shifted lines',(source.replace(r'\paragraph{Network.}',r'\paragraph{Network.}'+'\nAn editorial introduction to the network model.\n')).encode()),
              ('blank lines and comment',('% Editorial note.\n\n'+source).encode())]
    for name,content in positive:
        errors=validate(registry,content,True)
        if errors:failures.append(f'Positive control failed: {name}: '+ '; '.join(errors))
    before=current_occurrences(registry,paper)
    shifted=current_occurrences(registry,positive[-1][1])
    if any(b['start_line']+2!=a['start_line'] or b['printed_label']!=a['printed_label'] for b,a in zip(before,shifted)):
        failures.append('Live positions or printed numbers were not preserved under line shifts.')
    counter_fixture = r"""
\newtheorem{lemma}{Lemma}
\newtheorem{theorem}{Theorem}
\newtheorem{corollary}{Corollary}
\begin{lemma}First.\end{lemma}
\begin{lemma}Second.\end{lemma}
\edef\savedcounter{\number\value{lemma}}
\setcounter{lemma}{0}
\begin{lemma}Repeated first.\end{lemma}
\setcounter{lemma}{\savedcounter}
\begin{theorem}First theorem.\end{theorem}
\begin{lemma}Third.\end{lemma}
\begin{corollary}First corollary.\end{corollary}
\begin{theorem}Second theorem.\end{theorem}
"""
    expected = ['Lemma 1','Lemma 2','Lemma 1','Theorem 1','Lemma 3','Corollary 1','Theorem 2']
    if [o['printed_label'] for o in environments(counter_fixture)] != expected:
        failures.append('Independent/save/reset/restore counter control failed.')
    return failures


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--registry',type=Path,default=ROOT/'lean'/'claims.json')
    parser.add_argument('--paper',type=Path,default=ROOT/'paper.tex')
    parser.add_argument('--require-complete',action='store_true',help='Require the complete current registry (also the default).')
    parser.add_argument('--list-verified',action='store_true')
    parser.add_argument('--self-test',action='store_true')
    args=parser.parse_args()
    try:
        registry=json.loads(args.registry.read_text(encoding='utf-8'));paper=args.paper.read_bytes()
    except (OSError,ValueError) as exc:
        print(f'Claim registry could not be read: {exc}',file=sys.stderr);return 1
    errors=validate(registry,paper,args.require_complete)
    if not errors and args.self_test:errors+=self_test(registry,paper)
    if errors:
        print('\n'.join('ERROR: '+error for error in errors),file=sys.stderr);return 1
    names=sorted({name for c in registry['claims'] for name in c['lean_declarations']})
    if args.list_verified:
        print('\n'.join(names))
    else:
        print(f"Current registry valid: {len(registry['claims'])} proved records; {registry['paper']['formal_statement_count']} formal statements; {len(registry['theorem_occurrences'])} occurrences; {len(names)} declaration endpoints.")
        print('Paper: '+registry['paper']['title'])
        print('Registry structure and source coverage passed; Lean independently checks proof terms and transitive axioms.')
        if args.self_test:print('25 registry negative controls, three editorial positive controls and live-numbering controls passed.')
    return 0


if __name__=='__main__':
    raise SystemExit(main())
