#!/usr/bin/env python3
"""Check every registered proof endpoint in Lean after validating current scope."""
import json
from pathlib import Path

from check_claims import validate
from check_scope import audit_declarations, selected_declarations, validate_scope

ROOT = Path(__file__).resolve().parents[1]
registry = json.loads((ROOT / 'claims.json').read_text(encoding='utf-8'))
profile = json.loads((ROOT / 'scope.json').read_text(encoding='utf-8'))
errors = validate(registry, (ROOT.parent / 'paper.tex').read_bytes(), require_complete=True)
if not errors:
    errors += validate_scope(profile, registry)
if errors:
    raise SystemExit('\n'.join(errors))
names = selected_declarations(profile, registry)
audit_declarations(names)
print(f'Registry proof audit passed: {len(names)} actual declarations in the complete formal proof closure.')
