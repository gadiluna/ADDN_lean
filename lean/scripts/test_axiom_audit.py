#!/usr/bin/env python3
"""Exercise the trust gate with isolated, deliberately invalid temporary files."""
from pathlib import Path
import os
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]
PREFIX = "import Counting.AxiomAudit\n"
CASES = [
    ("standard proof", "theorem Counting.allowed : True := trivial\n#audit_project\n", True),
    ("unused project axiom", "axiom Counting.unused : True\n#audit_project\n", False),
    ("unused private axiom", "private axiom unused : True\n#audit_project\n", False),
    ("unused other-namespace axiom", "axiom Unrelated.unused : True\n#audit_project\n", False),
    ("private sorry proof", "private theorem unproved : False := by sorry\n"
     "#audit_project\n", False),
    ("direct sorry proof", "theorem Counting.unproved : False := by sorry\n"
     "#audit_project\n", False),
    ("direct axiom", "axiom Counting.unsound : False\n"
     "theorem Counting.rejected : False := Counting.unsound\n#audit_project\n", False),
    ("transitive private axiom", "axiom Foreign.unsound : False\n"
     "private theorem intermediary : False := Foreign.unsound\n"
     "theorem Counting.rejected : False := intermediary\n#audit_project\n", False),
    ("native evaluation", "theorem Counting.rejected : 2 + 2 = 4 := by native_decide\n"
     "#audit_project\n", False),
    ("missing declaration", "#audit_declaration Counting.doesNotExist\n", False),
    ("definition instead of theorem", "def Counting.notAProof : Nat := 3\n"
     "#audit_declaration Counting.notAProof\n", False),
]
for name, source, expected in CASES:
    with tempfile.NamedTemporaryFile(mode="w", suffix=".lean", dir=ROOT / ".lake",
                                     delete=False) as handle:
        handle.write(PREFIX + source)
        temporary = Path(handle.name)
    try:
        result = subprocess.run(["lake", "env", "lean", str(temporary)], cwd=ROOT,
                                capture_output=True, text=True)
    finally:
        temporary.unlink()
    if (result.returncode == 0) != expected:
        raise SystemExit(f"Unexpected audit result for {name}:\n{result.stdout}{result.stderr}")
    if not expected and not any(message in result.stdout + result.stderr for message in
                               ("Forbidden axiom", "does not exist", "not a proved theorem")):
        raise SystemExit(f"{name} failed for the wrong reason:\n{result.stdout}{result.stderr}")
# Exercise the imported-module branch separately. In the transitive case the
# foreign axiom's module is deliberately outside the project, so rejection
# must follow the imported project theorem's dependency, not a direct scan.
with tempfile.TemporaryDirectory(prefix='axiom-import-control-', dir=ROOT / '.lake') as directory:
    base = Path(directory)
    environment = os.environ.copy()
    project_path = subprocess.check_output(
        ['lake', 'env', 'printenv', 'LEAN_PATH'], cwd=ROOT, text=True).strip()
    environment['LEAN_PATH'] = str(base) + os.pathsep + project_path
    lean = subprocess.check_output(['lake', 'env', 'which', 'lean'], cwd=ROOT, text=True).strip()
    # Lean chooses a search root for the top-level module directory. Supply
    # the actual auditor beside the temporary Counting.* fixtures, and invoke
    # Lean directly so Lake does not prepend the normal Counting root again.
    (base / 'Counting').mkdir()
    for artifact in (ROOT / '.lake/build/lib/lean/Counting').glob('AxiomAudit.*'):
        (base / 'Counting' / artifact.name).symlink_to(artifact)
    modules = {
        'ForeignAuditControl': 'axiom ForeignAuditControl.unsound : False\n',
        'Counting.ImportedAuditAllowed': 'private theorem helper : True := trivial\n',
        'Counting.ImportedAuditPrivate': 'private axiom hidden : True\n',
        'Counting.ImportedAuditTransitive': 'import ForeignAuditControl\n'
            'namespace Unrelated\n'
            'private theorem helper : False := ForeignAuditControl.unsound\n'
            'theorem unsound : False := helper\nend Unrelated\n',
    }
    for module, source in modules.items():
        path = base / (module.replace('.', '/') + '.lean')
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(source)
        result = subprocess.run([lean, '--root=' + str(base),
                                 '-o', str(path.with_suffix('.olean')), str(path)],
                                cwd=ROOT, env=environment, capture_output=True, text=True)
        if result.returncode:
            raise SystemExit(f'Imported audit fixture did not compile: {module}\n'
                             f'{result.stdout}{result.stderr}')
    for module, expected in [('Counting.ImportedAuditAllowed', True),
                             ('Counting.ImportedAuditPrivate', False),
                             ('Counting.ImportedAuditTransitive', False)]:
        path = base / 'Check.lean'
        path.write_text(f'import Counting.AxiomAudit\nimport {module}\n#audit_project\n')
        result = subprocess.run([lean, '--root=' + str(base), str(path)],
                                cwd=ROOT, env=environment, capture_output=True, text=True)
        output = result.stdout + result.stderr
        if (result.returncode == 0) != expected or (not expected and 'Forbidden axiom' not in output):
            raise SystemExit(f'Unexpected imported audit result: {module}\n{output}')
        if module.endswith('Transitive') and 'Forbidden axiom declaration' in output:
            raise SystemExit('Transitive control was rejected by the direct scan, not dependency audit.')
print(f"Axiom-audit self-test passed: {len(CASES) + 3} positive/negative controls, "
      "including imported private declarations and transitive foreign assumptions.")
