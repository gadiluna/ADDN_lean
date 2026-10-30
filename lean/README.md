# Lean formalization

This project formalizes [Computation in Anonymous Directed Dynamic Networks: Exact Worst-Case Termination Time and Network-Wise Intractability](../paper.tex).
It proves every clause of the **24 distinct formal statements**, covering all
**26 lemma/theorem/corollary occurrences** and all required supporting results.

The [correspondence table](docs/PAPER_LEAN_CORRESPONDENCE.md) links each statement
to its printed number, complete statement and principal Lean declarations. The
[formal claim registry](docs/FORMAL_CLAIMS.md) lists the complete proof evidence;
[`claims.json`](claims.json) records exact source text and dependencies.
The [scope](docs/CURRENT_SCOPE.md) specifies the complete certification target.

## Build and verify

The project uses Lean **4.32.0** and mathlib **v4.32.0**, pinned to commit
`81a5d257c8e410db227a6665ed08f64fea08e997`. Every transitive package revision is
fixed in [`lake-manifest.json`](lake-manifest.json).

From this directory, with Elan installed:

```sh
elan toolchain install leanprover/lean4:v4.32.0
lake exe cache get
sh scripts/verify_semantic.sh
```

The verification command checks the formal statements and their numbering,
complete coverage, dependency revisions, all proof-bearing source modules, compilation,
transitive axiom dependencies, registered declarations, the correspondence
table and required executable regressions. See the
[verification guide](docs/VALIDATION.md).

Only `propext`, `Classical.choice` and `Quot.sound` are permitted axiom
dependencies. The audit rejects `sorryAx`, added mathematical axioms and
native-evaluation axioms. Warnings are errors.

## Model and executable interface

The [model and definitions table](docs/MODEL_AND_DEFINITIONS.md) links each
paper concept to its exact Lean definition, including histories, vistas,
realizability, the machine model and complexity classes.

Networks have finite agents and natural arc multiplicities. Parallel arcs and
self-loops are allowed. Strong connectivity is required in each communication
round; a singleton with zero arcs is admissible.

A local protocol receives the common leader count, its own leader role, its
state, received messages and the outgoing degree learned after sending the
previous state. A halted agent retains its answer and sends no messages.
Agent identities, true population, fibers and anonymities are proof data.

The executable stores views as shared DAGs with canonical signatures and
binary multiplicity counts. Both schedules, the five-step audit, the early
all-leader criterion and the exact rational solver have proved correspondence
with the mathematical specification. The complete Counting endpoints are:

- [`Counting.Paper.core_algorithm`](Counting/PaperFormalCounting.lean#L10)
- [`Counting.Paper.exact_termination`](Counting/PaperFormalCounting.lean#L38)

The local runtime theorem measures transitions of the verified finite-alphabet
Turing machine. It includes initialization and every live local transition,
starting from the encoded local state, binary-compressed received messages and
learned outdegree. Under the paper's exponential arc bound, total local time is
polynomial in the population. Raw packet aggregation, communication and input
tape preparation are outside that local interface; native simulator wall-clock
performance is measured separately.

## Source organization

| Sources | Role |
| --- | --- |
| `Counting/` | Distributed semantics, executable protocol, algebra, exact timing, lower bounds, realizability, reductions and machine-time proofs. |
| `DirectedCountingFormalization/` | [History, graph and algebra components](DirectedCountingFormalization/REUSE.md). |
| `Counting/AllProofs.lean` | Aggregate of the checked proof development. |
| `Audit.lean`, `Counting/AxiomAudit.lean` | Transitive theorem audit. |
| `scripts/` | Source, dependency, completeness and regression checks. |
| `examples/` | [Executable network inputs and traces](examples/README.md). |

To execute a network:

```sh
lake env lean --run Counting/Demo.lean examples/cycle3.json
```

The global harness validates the network and emits JSON snapshots. Agent
identities and actual population are confined to the harness and proof model.


## Regenerate the review documents

After building `Counting.AllProofs`:

```sh
python3 scripts/render_reports.py
python3 scripts/render_correspondence.py
```

Both generators have a `--check` mode used by the verification command. They
validate the current manuscript and registered evidence before producing the
formal registry, scope and correspondence table.
