#!/bin/sh
set -eu
cd "$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)"

# Run interpreter regressions after building Counting.AllProofs.
# Each suite has a configurable time limit and contributes to the exit status.
python3 - <<'PYRUN'
import os
import signal
import subprocess
import sys
import time

limit = int(os.environ.get("LEAN_ADDITIONAL_TEST_TIMEOUT_SECONDS", "120"))
if limit <= 0:
    raise SystemExit("LEAN_ADDITIONAL_TEST_TIMEOUT_SECONDS must be positive")
modules = [
    'Counting/MachineGaussianTests.lean',
    'Counting/MachinePositiveNaturalsTests.lean',
    'Counting/StackRealizabilityRoundTests.lean',
    'Counting/StackRealizabilityTotalTests.lean',
    'Counting/StackRealizabilityFixedOrderTests.lean',
    'Counting/StackRealizabilityVistaTests.lean',
    'Counting/InputMultisetTests.lean',
    'Counting/InputMultisetDagTests.lean',
    'Counting/InputMultisetCompactTests.lean',
    'Counting/MachineMatrixAxpyTests.lean',
    'Counting/MachineMatrixScaleTests.lean',
    'Counting/MachineRowDotTests.lean',
    'Counting/MachineRowOperationsTests.lean',
    'Counting/MachineRowScaleTests.lean',
    'Counting/NetworkVistaBundleFinishTests.lean',
    'Counting/NetworkVistaCollectPreservingTests.lean',
    'Counting/NetworkVistaCollectTests.lean',
    'Counting/NetworkVistaSenderTests.lean',
    'Counting/StackAuditDescendantPreservingTests.lean',
    'Counting/StackAuditDescendantQueryTests.lean',
    'Counting/StackAuditDescendantRoundsTests.lean',
    'Counting/StackAuditPrefixChildTests.lean',
    'Counting/StackAuditPropagationInitTests.lean',
    'Counting/StackDagAddCountStepTests.lean',
    'Counting/StackDagSortStepTests.lean',
    'Counting/StackRealizabilityArcPointTests.lean',
 ]
# A substring filter permits focused reruns without removing the full suite.
only = os.environ.get("LEAN_ADDITIONAL_TEST_FILTER", "")
if only:
    modules = [module for module in modules if only in module]
    if not modules:
        raise SystemExit("LEAN_ADDITIONAL_TEST_FILTER matched no suites")
failed = []
for module in modules:
    print(f"RUN {module} (wall limit {limit}s)", flush=True)
    start = time.monotonic()
    process = subprocess.Popen(["lake", "env", "lean", module], start_new_session=True)
    try:
        result = process.wait(timeout=limit)
    except KeyboardInterrupt:
        os.killpg(process.pid, signal.SIGTERM)
        try:
            process.wait(timeout=5)
        except subprocess.TimeoutExpired:
            os.killpg(process.pid, signal.SIGKILL)
            process.wait()
        print(f"INTERRUPTED {module}; not completed", flush=True)
        raise SystemExit(130)
    except subprocess.TimeoutExpired:
        os.killpg(process.pid, signal.SIGTERM)
        try:
            process.wait(timeout=5)
        except subprocess.TimeoutExpired:
            os.killpg(process.pid, signal.SIGKILL)
            process.wait()
        failed.append((module, "TIMEOUT"))
        print(f"TIMEOUT {module} after {time.monotonic()-start:.1f}s; not completed", flush=True)
        continue
    elapsed = time.monotonic()-start
    if result:
        failed.append((module, f"EXIT {result}"))
        print(f"FAIL {module} after {elapsed:.1f}s (exit {result})", flush=True)
    else:
        print(f"PASS {module} after {elapsed:.1f}s", flush=True)
print(f"Additional suites: {len(modules)-len(failed)}/{len(modules)} passed.", flush=True)
for module, reason in failed:
    print(f"INCOMPLETE {module}: {reason}", flush=True)
sys.exit(1 if failed else 0)
PYRUN
