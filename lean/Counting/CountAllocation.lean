import Counting.BalancedVertexCounts

/-! Constructing nested selected agent sets from the count inequalities.
The allocation is existential mathematics, separate from the compact verifier. -/

namespace Counting.CountAllocation

abbrev Slots {C : Type*} (count : C → Nat) := Σ c : C, Fin (count c)

/-- Finite objects can be placed into color-preserving slots whenever each
color's capacity dominates the cardinality of its fiber. -/
theorem exists_embedding_by_color {I C : Type*} [Fintype I] [DecidableEq C]
    (color : I → C) (capacity : C → Nat)
    (bound : ∀ c, Fintype.card {i : I // color i = c} ≤ capacity c) :
    ∃ e : I ↪ Slots capacity, ∀ i, (e i).1 = color i := by
  classical
  let within (c : C) : {i : I // color i = c} ↪ Fin (capacity c) :=
    Classical.choice (Function.Embedding.nonempty_of_card_le (by simpa using bound c))
  let e : I ↪ Slots capacity := (Equiv.sigmaFiberEquiv color).symm.toEmbedding.trans
    (Function.Embedding.sigmaMap (Function.Embedding.refl C) within)
  exact ⟨e, fun _ => rfl⟩

theorem slots_fiber_card {C D : Type*} [Fintype D] [DecidableEq C]
    (parent : D → C) (count : D → Nat) (c : C) :
    Fintype.card {i : Slots count // parent i.1 = c} =
      ∑ d ∈ Finset.univ.filter (fun d => parent d = c), count d := by
  classical
  rw [Fintype.card_subtype, Finset.card_eq_sum_ones, Finset.sum_filter]
  change (∑ i : (Σ d : D, Fin (count d)), if parent i.1 = c then 1 else 0) = _
  rw [Fintype.sum_sigma, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro d _
  by_cases hd : parent d = c <;> simp [hd]

/-- The count inequality below each old node is exactly the condition
needed for an injective placement of child slots inside parent slots. -/
theorem exists_refinement {C D : Type*} [Fintype D] [DecidableEq C]
    (parent : D → C) (oldCount : C → Nat) (newCount : D → Nat)
    (bound : ∀ c, (∑ d ∈ Finset.univ.filter (fun d => parent d = c), newCount d) ≤ oldCount c) :
    ∃ e : Slots newCount ↪ Slots oldCount, ∀ i, (e i).1 = parent i.1 := by
  apply exists_embedding_by_color (fun i : Slots newCount => parent i.1) oldCount
  intro c
  rw [slots_fiber_card]
  exact bound c

section Nested
variable {Node : Nat → Type*} [∀ r, Fintype (Node r)] [∀ r, DecidableEq (Node r)]
variable (parent : ∀ r, Node (r + 1) → Node r) (count : ∀ r, Node r → Nat)
variable (bound : ∀ r c,
  (∑ d ∈ Finset.univ.filter (fun d => parent r d = c), count (r + 1) d) ≤ count r c)

noncomputable def refinement (r : Nat) : Slots (count (r + 1)) ↪ Slots (count r) :=
  Classical.choose (exists_refinement (parent r) (count r) (count (r + 1)) (bound r))

theorem refinement_parent (r : Nat) (i : Slots (count (r + 1))) :
    (refinement parent count bound r i).1 = parent r i.1 :=
  Classical.choose_spec (exists_refinement (parent r) (count r) (count (r + 1)) (bound r)) i

/-- Once initial slots have been placed in the physical population, each
later slot names the same physical agent as its chosen parent slot. -/
noncomputable def allocation {A : Type*} (initial : Slots (count 0) ↪ A) :
    (r : Nat) → Slots (count r) ↪ A
  | 0 => initial
  | r + 1 => (refinement parent count bound r).trans (allocation initial r)

@[simp] theorem allocation_succ {A : Type*} (initial : Slots (count 0) ↪ A)
    (r : Nat) (i : Slots (count (r + 1))) :
    allocation parent count bound initial (r + 1) i =
      allocation parent count bound initial r (refinement parent count bound r i) := rfl

noncomputable def selected {A : Type*} (initial : Slots (count 0) ↪ A) (r : Nat) : Finset A := by
  classical
  exact Finset.univ.image (allocation parent count bound initial r)

noncomputable def group {A : Type*} (initial : Slots (count 0) ↪ A)
    (r : Nat) (c : Node r) : Finset A := by
  classical
  exact Finset.univ.image (fun j : Fin (count r c) => allocation parent count bound initial r ⟨c, j⟩)

theorem group_card {A : Type*} (initial : Slots (count 0) ↪ A) (r : Nat) (c : Node r) :
    (group parent count bound initial r c).card = count r c := by
  classical
  rw [group, Finset.card_image_of_injective]
  · simp
  · exact (allocation parent count bound initial r).injective.comp (Function.Embedding.sigmaMk c).injective

theorem selected_card {A : Type*} (initial : Slots (count 0) ↪ A) (r : Nat) :
    (selected parent count bound initial r).card = ∑ c : Node r, count r c := by
  classical
  rw [selected, Finset.card_image_of_injective _ (allocation parent count bound initial r).injective]
  simp [Slots, Fintype.card_sigma]

theorem group_subset_selected {A : Type*} (initial : Slots (count 0) ↪ A)
    (r : Nat) (c : Node r) : group parent count bound initial r c ⊆ selected parent count bound initial r := by
  classical
  intro a ha
  obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp ha
  exact Finset.mem_image.mpr ⟨⟨c, j⟩, Finset.mem_univ _, rfl⟩

theorem groups_disjoint {A : Type*} (initial : Slots (count 0) ↪ A)
    (r : Nat) {c d : Node r} (different : c ≠ d) :
    Disjoint (group parent count bound initial r c) (group parent count bound initial r d) := by
  classical
  apply Finset.disjoint_left.mpr
  intro a ha hb
  obtain ⟨i, _, hi⟩ := Finset.mem_image.mp ha
  obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hb
  have eq := (allocation parent count bound initial r).injective (hi.trans hj.symm)
  exact different (congrArg Sigma.fst eq)

theorem selected_nested {A : Type*} (initial : Slots (count 0) ↪ A) (r : Nat) :
    selected parent count bound initial (r + 1) ⊆ selected parent count bound initial r := by
  classical
  intro a ha
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp ha
  exact Finset.mem_image.mpr ⟨refinement parent count bound r i, Finset.mem_univ _, rfl⟩

/-- Each new selected group is a subset of its old parent group. -/
theorem group_subset_parent {A : Type*} (initial : Slots (count 0) ↪ A)
    (r : Nat) (c : Node (r + 1)) :
    group parent count bound initial (r + 1) c ⊆ group parent count bound initial r (parent r c) := by
  classical
  intro a ha
  obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp ha
  let old := refinement parent count bound r ⟨c, j⟩
  have ho : old.1 = parent r c := refinement_parent parent count bound r ⟨c, j⟩
  let index : Fin (count r (parent r c)) := ho ▸ old.2
  refine Finset.mem_image.mpr ⟨index, Finset.mem_univ _, ?_⟩
  rw [allocation_succ]
  apply congrArg (allocation parent count bound initial r)
  have transport : ∀ (x y : Node r) (eq : x = y) (i : Fin (count r x)),
      (⟨y, eq ▸ i⟩ : Slots (count r)) = ⟨x, i⟩ := by
    intro x y eq i
    cases eq
    rfl
  exact transport _ _ ho old.2

/-- A parent-preserved input label stays attached to the same physical
agent throughout the allocation. -/
theorem allocation_label {A B : Type*} (initial : Slots (count 0) ↪ A)
    (label : ∀ r, Node r → B) (agentLabel : A → B)
    (parentLabel : ∀ r c, label r (parent r c) = label (r + 1) c)
    (initialLabel : ∀ i, agentLabel (initial i) = label 0 i.1) :
    ∀ r i, agentLabel (allocation parent count bound initial r i) = label r i.1 := by
  intro r
  induction r with
  | zero => exact initialLabel
  | succ r ih =>
      intro i
      rw [allocation_succ, ih, refinement_parent]
      exact parentLabel r i.1

theorem selected_eq_union_groups {A : Type*} [DecidableEq A] (initial : Slots (count 0) ↪ A) (r : Nat) :
    selected parent count bound initial r = Finset.univ.biUnion (group parent count bound initial r) := by
  classical
  ext a
  simp only [selected, group, Finset.mem_image, Finset.mem_univ, true_and,
    Finset.mem_biUnion]
  constructor
  · rintro ⟨⟨c, j⟩, h⟩
    exact ⟨c, ⟨j, h⟩⟩
  · rintro ⟨c, j, h⟩
    exact ⟨⟨c, j⟩, h⟩

end Nested

/-- The actual N-agent carrier has ell leader slots and N-ell ordinary
slots. It is used only in the realization construction, never in a local
algorithm or in the efficient certificate verifier. -/
abbrev Population (N ell : Nat) := Slots (fun b : Bool => if b then ell else N - ell)

def populationLeader (N ell : Nat) (a : Population N ell) : Bool := a.1

theorem population_card (N ell : Nat) (feasible : ell ≤ N) :
    Fintype.card (Population N ell) = N := by
  simp [Population, Slots, Fintype.card_sigma]
  omega

theorem population_leaders (N ell : Nat) : leaderCount (populationLeader N ell) = ell := by
  unfold leaderCount populationLeader
  rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  change (∑ i : (Σ b : Bool, Fin (if b then ell else N - ell)), if i.1 = true then 1 else 0) = ell
  rw [Fintype.sum_sigma]
  simp [apply_ite]

/-- Initial selected slots fit in the N-agent population with exactly the
prescribed statuses whenever the two initial status budgets hold. -/
theorem exists_initial_allocation {C : Type*} [Fintype C]
    (count : C → Nat) (label : C → Bool) (N ell : Nat)
    (leaders : (∑ c ∈ Finset.univ.filter (fun c => label c = true), count c) ≤ ell)
    (ordinary : (∑ c ∈ Finset.univ.filter (fun c => label c = false), count c) ≤ N - ell) :
    ∃ initial : Slots count ↪ Population N ell,
      ∀ i, populationLeader N ell (initial i) = label i.1 := by
  apply exists_embedding_by_color (fun i : Slots count => label i.1)
    (fun b : Bool => if b then ell else N - ell)
  intro b
  rw [slots_fiber_card]
  cases b
  · exact ordinary
  · exact leaders

end Counting.CountAllocation
