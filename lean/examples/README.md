# Executable Lean demo

From `lean/`, build the harness and execute an input file:

```sh
lake build Counting.Simulation
lake env lean --run Counting/Demo.lean examples/cycle3.json
lake env lean --run Counting/Demo.lean examples/singleton.json
```

The input is a JSON object with `leaders`, a nonempty array of Boolean initial
leader labels, and `rounds`, an array of adjacency matrices. Entry
`rounds[t][sender][receiver]` is the number of parallel arcs in round `t + 1`.
Use JSON nonnegative integers; Lean retains arbitrary precision binary `Nat`
counts and does not expand a bundle into individual messages. Every matrix must
be square with one row and column per agent, and strongly connected. Self-loops
are allowed; a singleton with no arcs is connected. At least one leader is
required. The number of leaders is computed once and supplied to every local
state; global identities and the population are used only by this harness.

The program writes a JSON document containing a round-zero snapshot and one
snapshot for every supplied round, with each agent's output (`null` until
halted), vista depth, DAG node count, and DAG validity check. An input prefix may
end before termination; `all_halted: false` reports this without treating it as
an input error. No rounds are implicitly repeated. Halted agents stop sending
and retain their state in later snapshots. Invalid input gives a diagnostic on
standard error and exit code 1; incorrect command syntax gives exit code 2.

The three-agent example has two leaders and outputs 3 at round 4; round 5 shows
the frozen states. The singleton example outputs 1 at round 1 without messages.
These executions are demonstrations and regression checks. General equivalence
between the executable DAG representation and the mathematical protocol is
proved in the `Counting.DagSemantics*` and `Counting.ExecutableRefinement*`
modules. The [paper-to-Lean correspondence](../docs/PAPER_LEAN_CORRESPONDENCE.md)
maps all 24 distinct formal statements (26 occurrences), including every clause,
to their verified declarations. The [validation guide](../docs/VALIDATION.md)
describes the compilation, axiom and regression checks.
