# Scope of the formalization

**All 24 distinct formal statements are proved in full**, covering 26 lemma/theorem/corollary occurrences.

Paper: [Computation in Anonymous Directed Dynamic Networks: Exact Worst-Case Termination Time and Network-Wise Intractability](../../paper.tex) ([PDF](../../paper.pdf)).

The certification includes correctness, exact communication-round bounds, every stated graph restriction, encoded-size bounds, polynomial local computation, NP/coNP membership and both coNP-completeness results. All necessary external mathematical dependencies belong to the checked Lean proof closure.

## Coverage

| Item | Certified coverage |
| --- | --- |
| Distinct formal statements | 24 |
| Formal occurrences, including repeats | 26 |
| Required supporting results | 92 |
| Distinct registered proof declarations | 912 |
| Formal clauses | All |
| Transitive axioms allowed | `propext`, `Classical.choice`, `Quot.sound` |

The [paper–Lean correspondence](PAPER_LEAN_CORRESPONDENCE.md) provides the complete statement table and source links. [Validation](VALIDATION.md) explains the reproducible checks.

## Model and runtime interface

The model uses finite anonymous agents in changing strongly connected directed multigraphs, with loops and parallel arcs allowed. Agents know the leader count, send their previous state and then learn their outdegree; halted agents are silent. Agent identities and the true population occur only in the network model and proofs.

Local computation is measured in transitions of the verified finite-alphabet Turing machine. Each round receives encoded local state, binary-compressed messages and the learned outdegree. Initialization and every live local transition are charged. The general bound is polynomial in `n + bits(M) + 1`, where `M` bounds the total number of arcs in a round. The paper's `2^(poly(n))` arc bound makes total local time polynomial in `n`. Raw packet collection, physical communication and preparation of the external round input tape are outside this local input interface; native Lean, C and web execution times are not inferred from the finite-machine bound.

Complexity-class results use total binary input languages, concrete polynomial-time verifiers and reductions, and proved witness bounds. Malformed vistas have empty spectrum. Invalid network encodings are negative instances of `SomeAgentKnows`.

## Reproduce the certification

From `lean/`:

```sh
sh scripts/verify_semantic.sh
```

The command checks the source identification, exact source excerpts, complete formal coverage, dependency pins, source import coverage, aggregate compilation, transitive axioms, every registered declaration, all-clause scope and required regression suites. Registry labels alone are not proof evidence: the declaration audit imports the actual Lean declarations and checks their transitive assumptions.

References use the paper title, stable LaTeX labels and complete formal statement text. Line links and printed numbers are resolved from the current source, including the repeated Lemma 1 counter reset. Unrelated prose edits and whitespace reflow do not invalidate the formal statement certificate. Changed mathematical statements require review. 

This development targets the paper's formal statements and their required proof closure. Unnumbered observations and bibliographic comparisons are not independent certification obligations.
