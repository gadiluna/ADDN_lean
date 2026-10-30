# Formal claims registry

Generated from [claims.json](../claims.json) and [scope.json](../scope.json).

**All 24 distinct formal statements are proved in full**, covering 26 lemma/theorem/corollary occurrences.

Every clause and every required supporting result is included, including polynomial local runtime and the complexity-class conclusions.

Paper: [Computation in Anonymous Directed Dynamic Networks: Exact Worst-Case Termination Time and Network-Wise Intractability](../../paper.tex) ([PDF](../../paper.pdf)).

The [paper–Lean correspondence](PAPER_LEAN_CORRESPONDENCE.md) provides the complete statement table and source links. [Validation](VALIDATION.md) explains the reproducible checks.

## Complete statement coverage

| Printed number(s) | Formal statement | All paper occurrences | Coverage |
| --- | --- | --- | --- |
| Lemma 1 (repeated) | Flat level (`flat-level`) | [lines 486–491](../../paper.tex#L486), [lines 1343–1347](../../paper.tex#L1343) | Proved in full |
| Lemma 2 | Credit under refinement (`credit-refinement`) | [lines 592–600](../../paper.tex#L592) | Proved in full |
| Lemma 3 | Minimum-ratio closure (`minimum-ratio-closure`) | [lines 636–642](../../paper.tex#L636) | Proved in full |
| Lemma 4 | Credit loss (`credit-loss`) | [lines 692–697](../../paper.tex#L692) | Proved in full |
| Theorem 1 | Core algorithm (`core-algorithm`) | [lines 742–746](../../paper.tex#L742) | Proved in full |
| Theorem 2 | Exact termination time (`exact-termination`) | [lines 944–956](../../paper.tex#L944) | Proved in full |
| Theorem 3, Theorem 7 | Vista recognition is coNP-complete (`vista-complete`) | [lines 986–990](../../paper.tex#L986), [lines 2554–2557](../../paper.tex#L2554) | Proved in full |
| Lemma 5 | Tail exposure (`tail-exposure`) | [lines 1435–1440](../../paper.tex#L1435) | Proved in full |
| Lemma 6 | Fibers inside a proper subset (`forward-fibers`) | [lines 1465–1471](../../paper.tex#L1465) | Proved in full |
| Lemma 7 | Multi-leader test (`short-audit`) | [lines 1508–1512](../../paper.tex#L1508) | Proved in full |
| Lemma 8 | Two-center graph (`two-center`) | [lines 1630–1646](../../paper.tex#L1630) | Proved in full |
| Theorem 4 | Several-leader common vista (`several-leader-vista`) | [lines 1662–1669](../../paper.tex#L1662) | Proved in full |
| Lemma 9 | Bounded compatible orders (`bounded-orders`) | [lines 1894–1899](../../paper.tex#L1894) | Proved in full |
| Corollary 1 | Pumping and eventual compatibility (`pumping`) | [lines 1940–1956](../../paper.tex#L1940) | Proved in full |
| Lemma 10 | Eliminating a balanced auxiliary vertex (`balanced-vertex`) | [lines 1981–1989](../../paper.tex#L1981) | Proved in full |
| Lemma 11 | Realizing a transition (`full-transition-realizability`) | [lines 2013–2033](../../paper.tex#L2013) | Proved in full |
| Lemma 12 | Small full prefix (`small-full-prefix`) | [lines 2071–2082](../../paper.tex#L2071) | Proved in full |
| Lemma 13 | Fixed-order certificates (`fixed-order`) | [lines 2161–2166](../../paper.tex#L2161) | Proved in full |
| Theorem 5 | Vista recognition is in coNP (`vista-membership`) | [lines 2197–2201](../../paper.tex#L2197) | Proved in full |
| Theorem 6 | Network recognition is in coNP (`network-membership`) | [lines 2219–2222](../../paper.tex#L2219) | Proved in full |
| Lemma 14 | One reference solution, or an exact cover (`x3c-digits`) | [lines 2277–2289](../../paper.tex#L2277) | Proved in full |
| Lemma 15 | Common path prefix (`path-prefix`) | [lines 2349–2362](../../paper.tex#L2349) | Proved in full |
| Lemma 16 | The first visible level is full (`first-exhaustive`) | [lines 2443–2446](../../paper.tex#L2443) | Proved in full |
| Theorem 8 | Network recognition is coNP-complete (`network-complete`) | [lines 2570–2574](../../paper.tex#L2570) | Proved in full |

## Formal theorem evidence

Every declaration below is checked by the registry proof audit. The correspondence table identifies the principal theorem endpoints with direct Lean source links. The exact formal statements and all supporting declarations are retained in the JSON registry.

### Flat level

Source: [lines 486–491](../../paper.tex#L486), [lines 1343–1347](../../paper.tex#L1343).

- `Counting.FlatHistory.flat_iff_unique_child`
- `Counting.FlatHistory.flat_level_unique_solution`

### Credit under refinement

Source: [lines 592–600](../../paper.tex#L592).

- `Counting.CreditHistory.credit_under_refinement`
- `Counting.CreditHistory.credit_refinement_rigidity`

### Minimum-ratio closure

Source: [lines 636–642](../../paper.tex#L636).

- `Counting.CreditHistory.parent_closed_of_equal_fiber_unions`
- `Counting.CreditHistory.minimum_ratio_closure`

### Credit loss

Source: [lines 692–697](../../paper.tex#L692).

- `Counting.CreditHistory.PrefixChecks.credit_loss`

### Core algorithm

Source: [lines 742–746](../../paper.tex#L742).

- `Counting.TimingProtocol.core_solves_counting`
- `Counting.TimingProtocol.core_simultaneous`
- `Counting.Executable.executableCore_simultaneous`
- `Counting.Executable.binary_core_network_at_stop`
- `Counting.Paper.core_algorithm`

### Exact termination time

Source: [lines 944–956](../../paper.tex#L944).

- `Counting.exact_termination_optimal`
- `Counting.Executable.binary_network_at_stop`
- `Counting.Executable.executable_solves_counting`
- `Counting.Paper.exact_termination`

### Vista recognition is coNP-complete

Source: [lines 986–990](../../paper.tex#L986), [lines 2554–2557](../../paper.tex#L2554).

- `Counting.HardnessVistaRaw.AtMostOneVista_coNPComplete`
- `Counting.HardnessVistaRaw.AtMostOneVista_realizable_one_leader_hard`

### Tail exposure

Source: [lines 1435–1440](../../paper.tex#L1435).

- `Counting.causalSupport_card_lower_bound`
- `Counting.tail_exposure`

### Fibers inside a proper subset

Source: [lines 1465–1471](../../paper.tex#L1465).

- `Counting.ForwardFibers.fibers_inside_proper_subset`

### Multi-leader test

Source: [lines 1508–1512](../../paper.tex#L1508).

- `Counting.Executable.short_audit_reject_lt`
- `Counting.Executable.short_audit_accept_true`

### Two-center graph

Source: [lines 1630–1646](../../paper.tex#L1630).

- `Counting.TwoCenter.loopless`
- `Counting.TwoCenter.stronglyConnected`
- `Counting.TwoCenter.left_incoming`
- `Counting.TwoCenter.right_incoming`
- `Counting.TwoCenter.left_outdegree`
- `Counting.TwoCenter.right_outdegree`

### Several-leader common vista

Source: [lines 1662–1669](../../paper.tex#L1662).

- `Counting.LowerSeveral.several_leader_common_vista`
- `Counting.LowerSeveral.endpoint_common_prefix`
- `Counting.LowerSeveralExact.endpoint_first_difference`
- `Counting.LowerSeveral.several_leader_vista`
- `Counting.LowerSeveral.first_nonisomorphic_vistas`

### Bounded compatible orders

Source: [lines 1894–1899](../../paper.tex#L1894).

- `Counting.Realizability.bounded_compatible_orders`
- `Counting.Encoding.vistaInput_parameters`
- `Counting.Encoding.compatible_threshold_bits_encoded`

### Pumping and eventual compatibility

Source: [lines 1940–1956](../../paper.tex#L1940).

- `Counting.Realizability.pumping_of_open_realization`
- `Counting.Realizability.bounded_or_eventual`
- `Counting.Realizability.spectrum_finite_or_cofinite`

### Eliminating a balanced auxiliary vertex

Source: [lines 1981–1989](../../paper.tex#L1981).

- `Counting.BalancedVertex.remaining_path_of_no_incoming`
- `Counting.BalancedVertex.connected_of_remaining_reachable`
- `Counting.BalancedVertex.eliminate_balanced_vertex_of_remaining_reachable`
- `Counting.BalancedVertex.eliminate_at_vertex_of_remaining_reachable`

### Realizing a transition

Source: [lines 2013–2033](../../paper.tex#L2013).

- `Counting.FullTransition.agents_fiber_card`
- `Counting.FullTransition.agents_card`
- `Counting.FullTransition.agents_represented`
- `Counting.FullTransition.Data.Realizes.arc_of_positive`
- `Counting.FullTransition.Data.Realizes.node_connected`
- `Counting.FullTransition.Data.Realizes.necessary`
- `Counting.FullTransition.Data.red_zero_of_unoccupied`
- `Counting.FullTransition.Data.expanded_outdegree`
- `Counting.FullTransition.Data.expanded_receipts`
- `Counting.FullTransition.Data.aux_successor`
- `Counting.FullTransition.Data.nonempty_node_path`
- `Counting.FullTransition.Data.expanded_lift_edge`
- `Counting.FullTransition.Data.expanded_connected`
- `Counting.FullTransition.Data.sufficient`
- `Counting.FullTransition.Data.singleton`
- `Counting.FullTransition.Data.realizable_iff`
- `Counting.FullTransition.Data.weightedFlow_iff`
- `Counting.FullTransition.Data.realizing_transition`
- `Counting.FullTransition.Data.realizing_transition_singleton`

### Small full prefix

Source: [lines 2071–2082](../../paper.tex#L2071).

- `Counting.SmallPrefix.kept_add_lost`
- `Counting.SmallPrefix.normalize_visible`
- `Counting.SmallPrefix.normalize_row`
- `Counting.SmallPrefix.normalize_visible_degree`
- `Counting.SmallPrefix.normalize_hidden_degree`
- `Counting.SmallPrefix.normalize_hidden_column`
- `Counting.SmallPrefix.normalize_hidden_incoming`
- `Counting.SmallPrefix.normalize_connected`
- `Counting.SmallPrefix.normalize_hub_degree_le`
- `Counting.SmallPrefix.kept_le`
- `Counting.SmallPrefix.step_visible`
- `Counting.SmallPrefix.step_visible_degree`
- `Counting.SmallPrefix.step_connected`
- `Counting.SmallPrefix.step_degree_bound`
- `Counting.SmallPrefix.step_card`
- `Counting.SmallPrefix.mem_visibleAgents`
- `Counting.SmallPrefix.edge_le_receipt`
- `Counting.SmallPrefix.visible_source`
- `Counting.SmallPrefix.visible_edge_bound`
- `Counting.SmallPrefix.visible_degree_bound`
- `Counting.SmallPrefix.network_admissible`
- `Counting.SmallPrefix.network_history_visible`
- `Counting.SmallPrefix.network_observer`
- `Counting.SmallPrefix.network_level_step`
- `Counting.SmallPrefix.network_level_bound`
- `Counting.SmallPrefix.network_degree_bound`
- `Counting.SmallPrefix.degreeBound_le`
- `Counting.SmallPrefix.labelCap_bounds`
- `Counting.SmallPrefix.labelCap_size`
- `Counting.SmallPrefix.anonymity_le`
- `Counting.SmallPrefix.network_degree_label`
- `Counting.SmallPrefix.network_red_label`
- `Counting.SmallPrefix.network_labels`
- `Counting.SmallPrefix.depth_le_nodeCount`
- `Counting.SmallPrefix.network_level_uniform`
- `Counting.SmallPrefix.table_roundtrip`
- `Counting.SmallPrefix.fullLevel_list_nodup`
- `Counting.SmallPrefix.parent_in_fullLevel`
- `Counting.SmallPrefix.red_outside_fullLevel`
- `Counting.SmallPrefix.parent_index_correct`
- `Counting.SmallPrefix.table_level`
- `Counting.SmallPrefix.list_encoded_bound`
- `Counting.SmallPrefix.table_bits_bound`
- `Counting.SmallPrefix.fullLevel_card`
- `Counting.SmallPrefix.anonymity_nodeHistory`
- `Counting.SmallPrefix.network_spec`
- `Counting.SmallPrefix.small_full_prefix`
- `Counting.SmallPrefix.tableBudget_polynomial`
- `Counting.SmallPrefix.encoded_small_full_prefix`

### Fixed-order certificates

Source: [lines 2161–2166](../../paper.tex#L2161).

- `Counting.Realizability.fixed_order_iff_certificate`
- `Counting.Realizability.Certificate.count_le_order`
- `Counting.RealizabilityVerifier.exists_verified_iff`
- `Counting.RealizabilityVerifier.exists_bounded_verified`
- `Counting.Encoding.exists_encoded_bounded_certificate`
- `Counting.Encoding.binaryFixedOrder_bounded_witnesses`
- `Counting.StackMachine.FixedOrderRecognition.machine_computes`
- `Counting.StackMachine.FixedOrderRecognition.BinaryFixedOrderRealizable_in_NP`

### Vista recognition is in coNP

Source: [lines 2197–2201](../../paper.tex#L2197).

- `Counting.Realizability.not_atMostOne_iff_certificates`
- `Counting.Realizability.vista_complement_polynomial_witnesses`
- `Counting.Encoding.binaryVista_complement_iff`
- `Counting.StackMachine.VistaComplement.machine_computes`
- `Counting.StackMachine.VistaComplement.BinaryAtMostOneVista_in_coNP`

### Network recognition is in coNP

Source: [lines 2219–2222](../../paper.tex#L2219).

- `Counting.Realizability.not_someAgentKnows_iff_invalid_or_certificates`
- `Counting.Realizability.network_complement_payload_polynomial`
- `Counting.Encoding.binaryNetwork_complement_iff`
- `Counting.StackMachine.NetworkRecognition.networkValidationMachine_concrete`
- `Counting.StackMachine.NetworkRecognition.validNetworkWord_eq_decodeNetwork`
- `Counting.StackMachine.NetworkRecognition.admissibleNetworkLanguage_in_P`
- `Counting.StackMachine.NetworkComplement.BinarySomeAgentKnows_in_coNP`
- `Counting.StackMachine.NetworkComplement.machine_computes`
- `Counting.NetworkCertificate.binaryRawNetwork_complement_iff`

### One reference solution, or an exact cover

Source: [lines 2277–2289](../../paper.tex#L2277).

- `Counting.X3C.Instance.baseline_solution`
- `Counting.X3C.Instance.solution_iff`
- `Counting.X3C.Instance.option_coordinate_sum_le`
- `Counting.X3C.Instance.nonbaseline_solution_iff_exactCover`

### Common path prefix

Source: [lines 2349–2362](../../paper.tex#L2349).

- `Counting.HardnessPath.path_histories`
- `Counting.HardnessPath.physical_member_partition`
- `Counting.HardnessPath.physical_member_ne_leader`
- `Counting.HardnessPath.common_path_prefix`

### The first visible level is full

Source: [lines 2443–2446](../../paper.tex#L2443).

- `Counting.HardnessVisible.first_level_exhaustive`

### Network recognition is coNP-complete

Source: [lines 2570–2574](../../paper.tex#L2570).

- `Counting.NetworkComplement.SomeAgentKnows_coNPComplete`
- `Counting.NetworkComplement.SomeAgentKnows_one_leader_loopless_hard`

## Required supporting results

The formal statements require 92 supporting registry records. Together the 116 records cite 912 distinct proved declarations. The checker requires exactly this transitive dependency closure: no required result may be omitted, and no unproved result may be accepted as evidence.

Formal source links resolve the current exact statement. Supporting source links are optional contextual LaTeX labels; a supporting result without one identifies its role in the checked proof. The theorem names and dependency edges for every row are available in [claims.json](../claims.json).

| Supporting result | Current source or proof role | Required predecessors |
| --- | --- | --- |
| `model-network` — Finite directed multigraphs and nonempty-cut characterization of strong connectivity | [lines 264–264](../../paper.tex#L264) | — |
| `model-protocol` — Local deterministic protocol with late outdegree and silent halting | [lines 264–264](../../paper.tex#L264) | `model-network` |
| `history-refinement` — History partitions refine and preserve initial status | [lines 264–264](../../paper.tex#L264) | `model-network` |
| `same-history-same-state` — History equality implies equality of states for every protocol | [lines 264–264](../../paper.tex#L264), [lines 1585–1585](../../paper.tex#L1585) | `history-refinement`, `model-protocol` |
| `history-fibers` — History nodes have nonempty partition fibers and a unique parent | [lines 264–264](../../paper.tex#L264) | `history-refinement` |
| `history-labels` — Incoming multiplicities and outdegree labels are constant on fibers | [lines 264–264](../../paper.tex#L264) | `history-refinement` |
| `vista-isomorphism` — History equality is equivalent to labeled vista isomorphism | [lines 264–264](../../paper.tex#L264) | `history-fibers`, `history-labels`, `causal-visibility`, `same-history-same-state` |
| `vista-update` — Match-and-merge computes the observer vista while all agents remain active | [lines 264–264](../../paper.tex#L264) | `vista-isomorphism`, `model-protocol` |
| `vista-dag-refinement` — Shared DAG canonical signatures implement abstract vista match-and-merge | [lines 264–264](../../paper.tex#L264), [lines 503–503](../../paper.tex#L503) | `vista-isomorphism` |
| `exhaustive-prefix` — Fullness of one level implies fullness of all previous levels | [lines 264–264](../../paper.tex#L264) | `history-fibers`, `causal-visibility` |
| `h1-refinement` — H1: visible fibers are disjoint; child and total anonymity bounds with equality criteria | [lines 407–407](../../paper.tex#L407) | `history-fibers` |
| `h2-leaders` — H2: leader-status inheritance and leader anonymity accounting | [lines 407–407](../../paper.tex#L407) | `history-fibers`, `history-refinement` |
| `h3-flow` — H3 and Flow: exact arc counts and equality of incoming and outgoing totals | [lines 407–407](../../paper.tex#L407) | `history-labels`, `history-fibers` |
| `causal-visibility` — A node is visible iff its fiber meets the observer causal support | [lines 1404–1404](../../paper.tex#L1404) | `history-fibers`, `history-labels`, `history-refinement` |
| `causal-expansion` — Causal support is nested and strictly expands backward while proper | [lines 1404–1404](../../paper.tex#L1404), [lines 1427–1427](../../paper.tex#L1427) | `model-network`, `causal-visibility` |
| `h4-delay` — H4: level r is full whenever t >= r+n-1 | [lines 407–407](../../paper.tex#L407) | `causal-expansion`, `causal-visibility` |
| `positive-kernel` — An irreducible nonnegative-off-diagonal matrix with a positive kernel vector has a one-dimensional kernel | [lines 1330–1330](../../paper.tex#L1330) | — |
| `leader-normalization` — A positive leader-count equation uniquely fixes the kernel scale | [lines 1330–1330](../../paper.tex#L1330) | `h2-leaders`, `positive-kernel` |
| `candidate-test` — The five-step candidate test and rejection conditions | [lines 503–503](../../paper.tex#L503) | `vista-dag-refinement`, `exact-gaussian` |
| `candidate-conservation` — Backward propagation preserves candidate total and leader total at every earlier level | [lines 503–503](../../paper.tex#L503) | `history-fibers`, `h2-leaders` |
| `credit-initial-bound` — Initial total credit is at most m-1 | [lines 503–503](../../paper.tex#L503) | `candidate-conservation`, `h2-leaders` |
| `suffix-credit` — Passing the suffix test forces credit at least the increase in visible node count | [lines 503–503](../../paper.tex#L503) | `h1-refinement`, `history-fibers` |
| `nonflat-growth` — Each nonflat transition with a visible child per parent increases node count | [lines 503–503](../../paper.tex#L503) | `h1-refinement` |
| `core-reject-false` — Every candidate m<n is rejected by the core test | [lines 503–503](../../paper.tex#L503) | `credit-loss`, `credit-initial-bound`, `suffix-credit`, `nonflat-growth`, `candidate-test`, `vista-update` |
| `flat-exists` — A full n-level prefix contains a flat level | [lines 503–503](../../paper.tex#L503) | `history-fibers`, `nonflat-growth` |
| `core-accept-true` — Candidate n passes every core-test check at round 2n-1 | [lines 503–503](../../paper.tex#L503) | `flat-level`, `flat-exists`, `exhaustive-prefix`, `h3-flow`, `candidate-test` |
| `core-simultaneous` — No agent halts before the core true-candidate test; all halt there together | [lines 503–503](../../paper.tex#L503) | `core-reject-false`, `core-accept-true`, `vista-update`, `model-protocol` |
| `one-system` — Each candidate test solves at most one linear system with at most n variables | [lines 503–503](../../paper.tex#L503) | `candidate-test`, `h1-refinement` |
| `exact-gaussian` — Exact rational Gaussian elimination is correct and complete for uniqueness, positivity and integrality checks | [lines 503–503](../../paper.tex#L503) | `vista-dag-refinement` |
| `binary-label-bound` — The arc bound implies polynomial bit length for labels and coefficients | [lines 503–503](../../paper.tex#L503) | `vista-dag-refinement`, `h3-flow` |
| `gaussian-bit-cost` — Reduced exact Gaussian elimination has polynomial bit complexity | [lines 503–503](../../paper.tex#L503) | `exact-gaussian`, `machine-arithmetic` |
| `vista-size-cost` — Vista construction and all non-solver checks have polynomial size and bit cost | [lines 503–503](../../paper.tex#L503) | `vista-dag-refinement`, `machine-graphs`, `machine-arithmetic`, `one-system` |
| `core-bit-cost` — The complete counting algorithm has polynomial local bit cost under the paper arc bound | [lines 503–503](../../paper.tex#L503), [lines 803–803](../../paper.tex#L803) | `binary-label-bound`, `gaussian-bit-cost`, `vista-size-cost`, `one-system` |
| `all-leader-test` — The round-ell no-nonleader test succeeds exactly when n=ell | [lines 803–803](../../paper.tex#L803), [lines 1427–1427](../../paper.tex#L1427) | `h2-leaders`, `causal-visibility`, `model-network` |
| `short-credit-rigidity` — Equality in the shorter credit audit forces singleton final fibers and correct anchor counts | [lines 1427–1427](../../paper.tex#L1427) | `credit-loss`, `suffix-credit`, `nonflat-growth`, `tail-exposure`, `candidate-conservation` |
| `short-anchor-last` — A false passing shorter audit must have h=m-1 | [lines 1427–1427](../../paper.tex#L1427) | `short-credit-rigidity`, `model-network` |
| `short-flow-closure` — Backward candidate counts count intersections with S; full fibers in S send only into S | [lines 1427–1427](../../paper.tex#L1427) | `short-anchor-last`, `h3-flow`, `candidate-conservation` |
| `short-accept-true` — The shorter audit accepts the true order n>ell at round 2n-2 | [lines 1427–1427](../../paper.tex#L1427), [lines 803–803](../../paper.tex#L803) | `h4-delay`, `flat-level`, `nonflat-growth`, `candidate-test` |
| `optimized-simultaneous` — Combining all-leader and core/short tests gives the stated simultaneous halting times | [lines 1427–1427](../../paper.tex#L1427) | `all-leader-test`, `core-reject-false`, `core-accept-true`, `short-audit`, `model-protocol`, `vista-update`, `candidate-test` |
| `lower-all-leader-path` — The two all-leader-path instances have matching endpoint histories through n-1 | [lines 1585–1585](../../paper.tex#L1585), [lines 803–803](../../paper.tex#L803) | `same-history-same-state`, `model-network`, `lower-universal` |
| `lower-one-leader-path` — Looped endpoint paths of orders n and n+1 match through 2n-2 | [lines 1585–1585](../../paper.tex#L1585), [lines 803–803](../../paper.tex#L803) | `same-history-same-state`, `model-network`, `lower-universal` |
| `lower-phase-one` — First several-leader phase preserves the specified leader and nonleader matches | [lines 1585–1585](../../paper.tex#L1585), [lines 803–803](../../paper.tex#L803) | `two-center`, `same-history-same-state`, `model-network` |
| `lower-phase-two` — Second several-leader phase preserves matches until each selected center is retired | [lines 1585–1585](../../paper.tex#L1585), [lines 803–803](../../paper.tex#L803) | `lower-phase-one`, `two-center`, `same-history-same-state` |
| `lower-initial-relays` — g initial relay rounds preserve corresponding relay and core matches | [lines 1585–1585](../../paper.tex#L1585), [lines 803–803](../../paper.tex#L803) | `model-network`, `same-history-same-state` |
| `lower-middle-relays` — Substituting the relay fanout preserves outdegrees, connectivity and both phase invariants | [lines 1585–1585](../../paper.tex#L1585), [lines 803–803](../../paper.tex#L803) | `lower-initial-relays`, `lower-phase-one`, `lower-phase-two` |
| `lower-final-cycle` — The fixed final cycles preserve observer histories for exactly g+1 final rounds | [lines 1585–1585](../../paper.tex#L1585), [lines 803–803](../../paper.tex#L803) | `lower-middle-relays`, `same-history-same-state`, `model-network` |
| `lower-structural-bounds` — Several-leader construction is loopless with multiplicities <=ell and outdegrees <=ell^2 | [lines 1585–1585](../../paper.tex#L1585), [lines 803–803](../../paper.tex#L803) | `two-center`, `lower-middle-relays`, `lower-initial-relays`, `lower-final-cycle` |
| `lower-universal` — Equal full-information vistas in different orders prevent termination for any correct protocol | [lines 1585–1585](../../paper.tex#L1585), [lines 803–803](../../paper.tex#L803) | `same-history-same-state`, `model-protocol` |
| `lower-combined` — The three constructions imply the three universal lower bounds | [lines 1585–1585](../../paper.tex#L1585), [lines 803–803](../../paper.tex#L803), [lines 945–945](../../paper.tex#L945) | `lower-universal`, `lower-all-leader-path`, `lower-one-leader-path`, `lower-phase-one`, `lower-phase-two`, `lower-initial-relays`, `lower-middle-relays`, `lower-final-cycle`, `lower-structural-bounds` |
| `spectrum-knowledge` — On realizable vistas, knowing the order is equivalent to a singleton spectrum | [lines 959–959](../../paper.tex#L959), [lines 1838–1838](../../paper.tex#L1838) | `vista-isomorphism`, `same-history-same-state` |
| `vista-syntax` — Syntactic vista validation is polynomial-time decidable | [lines 1838–1838](../../paper.tex#L1838) | — |
| `certificate-nesting` — Selected-count inequalities admit nested selected agent sets with prescribed types | Allocation lemma for the selected-count certificate proof of fixed-order realizability. | `history-fibers` |
| `certificate-test` — Executable fixed-order verifier implements count, balance and auxiliary-connectivity tests | Executable selected-count certificate verifier used to prove fixed-order NP membership and recognition coNP membership. | `vista-dag-refinement`, `certificate-necessary`, `certificate-sufficient`, `certificate-singleton` |
| `certificate-necessary` — Causal support of a realization supplies a passing count certificate | Necessity direction of the selected-count certificate characterization of fixed-order realizability. | `causal-visibility`, `causal-expansion`, `h3-flow`, `vista-isomorphism` |
| `certificate-auxiliary-balance` — The expanded physical graph balances every auxiliary vertex | Auxiliary-vertex balance invariant in the physical construction from a selected-count certificate. | `certificate-nesting` |
| `certificate-auxiliary-connected` — Strong connectivity of the type graph lifts to the expanded physical graph | Connectivity lifting lemma in the physical construction from a selected-count certificate. | `certificate-auxiliary-balance`, `model-network` |
| `certificate-elimination` — Eliminating auxiliary vertices preserves selected degrees, receipts and causal exclusion | Degree, receipt and causal-support preservation in the auxiliary-vertex construction of a realization. | `balanced-vertex-strong`, `certificate-auxiliary-connected` |
| `certificate-sufficient` — Passing counts construct a realization with exactly the requested observer vista | Sufficiency direction of the selected-count certificate characterization of fixed-order realizability. | `certificate-nesting`, `certificate-elimination`, `certificate-singleton`, `vista-isomorphism` |
| `certificate-singleton` — For N=1 the certificate is realized by the indicated number of self-loops, including zero | Singleton realization case of the selected-count certificate characterization. | `certificate-nesting`, `vista-isomorphism` |
| `certificate-size-cost` — Count certificates have O(nu log(N+1)) bits and polynomial verification time | Witness-size and verification-time bounds for the selected-count certificate implementation. | `certificate-test`, `certificate-nesting`, `vista-syntax`, `machine-arithmetic` |
| `causal-support-bound` — Every realization has initial causal support at most K=(1+nu M)^t | [lines 1838–1838](../../paper.tex#L1838), [lines 996–996](../../paper.tex#L996) | `causal-visibility`, `causal-expansion` |
| `causal-bound-bitlength` — K and K+ell+2 have polynomial bit length in the explicit vista input | [lines 1895–1895](../../paper.tex#L1895), [lines 1838–1838](../../paper.tex#L1838) | `causal-support-bound`, `vista-dag-refinement`, `certificate-test` |
| `open-certificate-invariance` — An open realization certificate passes at every order N>=K+ell+1 | Order-extension lemma supporting the formal pumping and eventual-compatibility corollary. | `certificate-necessary`, `certificate-sufficient`, `causal-support-bound` |
| `pumping-from-order` — An open realization of order N realizes every order N+h | [lines 1838–1838](../../paper.tex#L1838) | `certificate-necessary`, `certificate-sufficient` |
| `finite-or-cofinite` — Every order spectrum is finite or cofinite with the stated threshold bound | [lines 1838–1838](../../paper.tex#L1838) | `pumping-from-order`, `causal-support-bound`, `certificate-sufficient` |
| `explicit-network-vistas` — Explicit binary-multiplicity networks yield all final vistas in polynomial time | [lines 1838–1838](../../paper.tex#L1838) | `vista-dag-refinement`, `machine-graphs`, `machine-arithmetic` |
| `network-complement-certificate` — A no-instance of SomeAgentKnows has one bounded alternate-order certificate per agent | [lines 1838–1838](../../paper.tex#L1838) | `bounded-orders`, `certificate-test`, `vista-dag-refinement`, `spectrum-knowledge`, `causal-bound-bitlength` |
| `x3c-normalization` — Deleting duplicate triples and padding to q>=2 preserves exact cover in polynomial time | [lines 2241–2241](../../paper.tex#L2241) | `machine-arithmetic` |
| `x3c-coefficients` — Exact-cover coefficients have the positivity, distinctness and size inequalities used in the reduction | [lines 2241–2241](../../paper.tex#L2241) | — |
| `x3c-no-carries` — Nonbaseline solutions have at most q summands; base-B digits force exact cover | [lines 2241–2241](../../paper.tex#L2241) | `x3c-coefficients` |
| `baseline-weight` — Baseline group sizes give order N0=R+1 and weighted total C | [lines 2241–2241](../../paper.tex#L2241) | `x3c-coefficients` |
| `path-graph-valid` — Repeated path graphs and the baseline ordinary star are strongly connected and loopless with the stated degrees | [lines 2241–2241](../../paper.tex#L2241) | `baseline-weight`, `model-network` |
| `baseline-final-visible` — The ordinary star exposes all B nonleader nodes per group and all earlier ancestors | [lines 2241–2241](../../paper.tex#L2241) | `path-prefix`, `path-graph-valid`, `exhaustive-prefix` |
| `reduction-bit-cost` — The baseline network and vista reductions have polynomial binary encoding size and construction time | [lines 2241–2241](../../paper.tex#L2241) | `x3c-coefficients`, `baseline-weight`, `explicit-network-vistas`, `machine-arithmetic`, `machine-graphs` |
| `visible-set-bounds` — Any realization satisfies a_i>=B, weighted inequality and R<=\|S_(B-1)\|<=\|S_1\|<=R+q | [lines 2440–2440](../../paper.tex#L2440) | `baseline-final-visible`, `h1-refinement`, `h3-flow`, `x3c-coefficients` |
| `exhaustive-exact-equation` — Full first level turns the leader outdegree inequality into the exact-cover equation | [lines 2241–2241](../../paper.tex#L2241) | `first-exhaustive`, `h3-flow`, `x3c-digits` |
| `alternate-group-weight` — An exact cover gives order N1=N0+q-1 and the same weighted group total C | [lines 2241–2241](../../paper.tex#L2241) | `x3c-digits`, `baseline-weight` |
| `alternate-leader` — Adjusted final graph reproduces the baseline leader vista at order N1 | [lines 2241–2241](../../paper.tex#L2241) | `alternate-group-weight`, `vista-isomorphism`, `path-graph-valid` |
| `alternate-nonleaders` — An ordinary-star alternate final graph simultaneously reproduces every baseline nonleader vista | [lines 2241–2241](../../paper.tex#L2241) | `alternate-group-weight`, `vista-isomorphism` |
| `reduction-spectrum` — The reduction spectrum is {N0} without an exact cover and {N0,N1} with one | [lines 2241–2241](../../paper.tex#L2241) | `exhaustive-exact-equation`, `alternate-leader`, `baseline-final-visible` |
| `vista-hardness` — Complement-X3C reduces in polynomial time to AtMostOneVista on realizable one-leader vistas | [lines 2241–2241](../../paper.tex#L2241) | `reduction-spectrum`, `reduction-bit-cost`, `x3c-np-complete` |
| `network-hardness` — Complement-X3C reduces to SomeAgentKnows on loopless one-leader networks | [lines 2241–2241](../../paper.tex#L2241) | `alternate-leader`, `alternate-nonleaders`, `reduction-spectrum`, `x3c-normalization`, `matching-to-x3c`, `x3c-coefficients`, `machine-arithmetic`, `complexity-complements` |
| `machine-model` — Fixed finite-alphabet Turing-machine cost model and simulation of executable Lean routines | Finite-alphabet machine and verified simulation foundations used to interpret every complexity and local-runtime statement. | — |
| `machine-arithmetic` — Polynomial bit-cost primitives for binary natural, integer and rational arithmetic | [lines 503–503](../../paper.tex#L503) | — |
| `machine-graphs` — Polynomial bit-cost primitives for finite graph validation, reachability and canonical partition construction | [lines 1838–1838](../../paper.tex#L1838) | `machine-model`, `machine-arithmetic` |
| `complexity-complements` — Polynomial reductions, NP/coNP complement laws and consequence of P != NP | [lines 987–987](../../paper.tex#L987), [lines 1838–1838](../../paper.tex#L1838) | — |
| `cook-levin` — Cook-Levin: satisfiability is NP-complete in the fixed machine model | [lines 2241–2241](../../paper.tex#L2241) | — |
| `sat-to-three-sat` — Polynomial equisatisfiable SAT-to-3SAT reduction and 3SAT NP-completeness | [lines 2241–2241](../../paper.tex#L2241) | `cook-levin`, `machine-arithmetic` |
| `three-sat-to-matching` — Polynomial 3SAT-to-three-dimensional-matching reduction | [lines 2241–2241](../../paper.tex#L2241) | `sat-to-three-sat` |
| `matching-to-x3c` — Polynomial three-dimensional-matching-to-X3C reduction | [lines 2241–2241](../../paper.tex#L2241) | `three-sat-to-matching` |
| `x3c-np-complete` — X3C NP-completeness for explicit-universe binary encoding | [lines 2241–2241](../../paper.tex#L2241), [lines 1061–1061](../../paper.tex#L1061) | `matching-to-x3c`, `machine-arithmetic` |
| `balanced-vertex-strong` — Balanced-vertex elimination under whole-graph strong connectivity | Whole-graph connectivity form of balanced-vertex elimination used by the realization constructions. | `model-network` |

## Certification interface

The target is every clause of every formal lemma, theorem and corollary and all proof dependencies required for those results. The proof may use a different argument from the prose proof. The [scope](CURRENT_SCOPE.md) specifies the model and runtime interface. The only permitted transitive axioms are `propext`, `Classical.choice` and `Quot.sound`.
