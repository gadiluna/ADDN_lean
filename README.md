# Computation in Anonymous Directed Dynamic Networks: Exact Worst-Case Termination Time and Network-Wise Intractability

This repository contains the Lean formalization and accompanying paper.
The formalization covers every clause of the paper's 24 distinct formal
lemma, theorem and corollary statements, appearing in 26 occurrences,
together with their required mathematical dependencies.

| Material | Entry point |
| --- | --- |
| Paper | [PDF](paper.pdf) · [LaTeX source](paper.tex) · [Bibliography](references.bib) |
| Model and definitions | [Paper concepts and exact Lean definitions](lean/docs/MODEL_AND_DEFINITIONS.md) |
| Paper–Lean correspondence | [Printed numbers, complete statements and Lean proofs](lean/docs/PAPER_LEAN_CORRESPONDENCE.md) |
| Formal proof registry | [Formal claims](lean/docs/FORMAL_CLAIMS.md) |
| Lean project | [Build and model](lean/README.md) · [Verification](lean/docs/VALIDATION.md) |
| Certification scope | [Scope and assumptions](lean/docs/CURRENT_SCOPE.md) |

## Build and verify

Install Elan, then run:

```sh
cd lean
elan toolchain install leanprover/lean4:v4.32.0
lake exe cache get
sh scripts/verify_semantic.sh
```

The project fixes Lean 4.32.0 and all package revisions. The verification
checks compilation, complete formal-statement coverage, registered proof
declarations, transitive axiom dependencies and executable regressions.
Only `propext`, `Classical.choice` and `Quot.sound` are permitted axioms.

See the [verification guide](lean/docs/VALIDATION.md) for the checks and the
[Lean documentation](lean/README.md) for the model and executable interface.
