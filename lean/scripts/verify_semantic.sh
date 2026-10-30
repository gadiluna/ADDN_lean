#!/bin/sh
set -eu
cd "$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)"
python3 scripts/check_claims.py --self-test
python3 scripts/render_reports.py --check
python3 scripts/check_dependencies.py
python3 scripts/check_audit_coverage.py --self-test
lake build Counting.AllProofs Counting.AxiomAudit Counting.FullTransitionExamples \
  Counting.SmallPrefixExamples Counting.HardnessEncodedTests Counting.StackDagTestRun
python3 scripts/render_correspondence.py --check --self-test
lake env lean Audit.lean
python3 scripts/test_axiom_audit.py
python3 scripts/check_scope.py --audit --self-test --require-complete
python3 scripts/verify_registry.py
lake env lean Counting/ExecutableTests.lean
lake env lean Counting/ExecutableRefinementCoreTests.lean
lake env lean Counting/RealizabilityVerifierExamples.lean
lake env lean Counting/FullTransitionExamples.lean
lake env lean Counting/SmallPrefixExamples.lean
lake env lean Counting/ExternalExamples.lean
lake env lean Counting/EncodingNetworkTests.lean
lake env lean Counting/EncodingNetworkRecognitionTests.lean
lake env lean Counting/HardnessEncodedTests.lean
lake env lean Counting/HardnessEncodedReductionTests.lean
printf '%s\n' 'Full formal-statement verification passed: every clause of every lemma, theorem, and corollary is certified, including runtime and complexity claims. Unnumbered observations are not independent completion obligations.'
