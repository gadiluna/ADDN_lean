# Dependency proof components

This directory supplies the graph, history, algebra and certificate components
used by the Counting formalization. Every source file is rebuilt with the pinned
Lean and mathlib dependencies and included in the project axiom audit.

| Components | Role in the formalization |
|---|---|
| `MultigraphHistoryModel`, `WeightedEdgeCounting`, `PaperHistory` | Natural arc multiplicities, late-outdegree histories, finite fibers, parent maps and flow identities. |
| `Connectivity`, `Flooding`, `PairedHistory`, `MultigraphPairedHistory`, `MultigraphPairedRefinement` | Strong connectivity, dissemination, temporal paths and comparison of histories across executions. |
| `CrossExecutionMatrix`, `CrossExecutionPotential`, `MatrixUniqueness` | Matrix and potential arguments used by the history and certificate proofs. |
| `VerifiedGaussianAnchorSolver`, `GaussianGeneratorCompleteness` | Soundness and completeness components for exact rational linear solving. |
| Certificate and checker modules | Arithmetic, prefix, branching and connectivity properties used by the solver dependency closure. |

The `Counting/` modules connect these components to the paper's directed
multi-leader model, executable protocol, exact termination bounds, realizability
and complexity statements. The
[paper-to-Lean correspondence](../docs/PAPER_LEAN_CORRESPONDENCE.md) lists the
verified declarations for all 24 distinct formal statements (26 occurrences),
including every clause. The [validation guide](../docs/VALIDATION.md) gives the
commands for checking the complete development.

These proof components are attributed to the paper's author. Their declarations
and dependencies are checked directly by Lean.
