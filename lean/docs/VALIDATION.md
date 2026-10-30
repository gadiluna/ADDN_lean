# Verifying the formalization

The formalization accompanies [Computation in Anonymous Directed Dynamic Networks: Exact Worst-Case Termination Time and Network-Wise Intractability](../../paper.tex).
Run the complete verification from `lean/`:

```sh
sh scripts/verify_semantic.sh
```

A successful run certifies every clause of all **24 distinct formal statements**
and all necessary supporting results. The [correspondence table](PAPER_LEAN_CORRESPONDENCE.md)
covers their **26 occurrences** and links directly to the Lean declarations.

## Checks performed

| Check | Requirement |
| --- | --- |
| Paper reference | The paper is identified by its title; numbered formal statements are read from its LaTeX source. |
| Formal inventory | Every lemma, theorem and corollary occurrence is registered, including repeated statements. |
| Completeness | Every formal statement and its transitive supporting results have checked proof declarations. |
| Dependencies | Lean 4.32.0, mathlib v4.32.0 and all locked package revisions match their clean local sources. |
| Source coverage | Every proof-bearing project module belongs to the audit import closure. |
| Compilation | The complete aggregate and required test modules compile with warnings treated as errors. |
| Trust | Every project theorem and every registered proof endpoint passes the transitive axiom audit. |
| Correspondence | Every table row gives the printed number and full statement, and maps to registered Lean theorem constants. |
| Negative controls | Invalid source, scope, inventory, correspondence and axiom fixtures are rejected. |
| Regressions | Counting, solver/DAG boundaries, realizability, full transitions, compact prefixes, encodings and both hardness reductions pass their required executable checks. |

The only permitted transitive axioms are `propext`, `Classical.choice` and
`Quot.sound`. The audit rejects `sorryAx`, added mathematical axioms and
native-evaluation axioms.

The registry preserves the full statements, including graph restrictions,
representation bounds, singleton cases, exact timing, polynomial runtime and
complexity-class conclusions. Bibliographic comparisons and unnumbered
observations are outside the formal-statement target. The
[scope document](CURRENT_SCOPE.md) states the runtime input convention.

## Additional executable checks

`sh scripts/verify.sh` runs the extended component regression suite.
`sh scripts/verify_additional_tests.sh` runs further interpreter suites with a
per-suite time limit, configured by `LEAN_ADDITIONAL_TEST_TIMEOUT_SECONDS`.
A timeout or failed test causes a nonzero exit status. Finite test execution
complements the general Lean proofs; it does not establish their conclusions.

The checking commands use the current statements and registry directly.
Edits to surrounding prose do not change the formal-statement correspondence.
No saved execution log is required for verification.
