import Counting.VistaIsomorphism

/-! Transport between the actual visible quotient nodes of an execution
and the intrinsic canonical vista. The population and graph are used only
in this semantic identification, never as extra labels of an isomorphism. -/

namespace Counting.VistaIsomorphism
open DirectedCounting TimingProtocolLocal

abbrev ActualNode {V : Type} [Fintype V] (G : Nat → V → V → Nat) (labels : V → Bool)
    (t : Nat) (observer : V) (r : Nat) :=
  {c : PaperHistory.Node G labels r // r ≤ t ∧ c ∈ CoreTiming.levelsAt G labels t observer r}

variable {V W : Type} [Fintype V] [Fintype W]
variable (G : Nat → V → V → Nat) (H : Nat → W → W → Nat)
variable (labels : V → Bool) (labels' : W → Bool) (t : Nat) (x : V) (y : W)

noncomputable def observerNode : ActualNode G labels t x t :=
  ⟨PaperHistory.classOf G labels t x, le_rfl, by
    classical
    unfold CoreTiming.levelsAt visibleNodes
    rw [Nat.sub_self]
    exact Finset.mem_image.mpr ⟨x,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, TemporalReach.zero⟩, rfl⟩⟩

noncomputable def actualToCanonical (r : Nat) (a : ActualNode G labels t x r) :
    Node (history G labels t x) r :=
  ⟨nodeHistory G labels r a.val, by
    rw [levels_eq_image G labels t r a.property.1 x]
    exact Finset.mem_image.mpr ⟨a.val, a.property.2, rfl⟩⟩

theorem actualToCanonical_bijective (r : Nat) : Function.Bijective (actualToCanonical G labels t x r) := by
  constructor
  · intro a b eq
    exact Subtype.ext (nodeHistory_injective G labels r (congrArg Subtype.val eq))
  · rintro ⟨h, hvisible⟩
    have visible := hvisible
    have hr : r ≤ t := by
      by_contra ht
      rw [levels_above t r _ (by omega)] at visible
      exact Finset.notMem_empty _ visible
    rw [levels_eq_image G labels t r hr x] at visible
    obtain ⟨c, hc, heq⟩ := Finset.mem_image.mp visible
    exact ⟨⟨c, hr, hc⟩, Subtype.ext heq⟩

noncomputable def actualNodeEquiv (r : Nat) : ActualNode G labels t x r ≃ Node (history G labels t x) r :=
  Equiv.ofBijective (actualToCanonical G labels t x r) (actualToCanonical_bijective G labels t x r)

@[simp] theorem actualNodeEquiv_val (r : Nat) (a : ActualNode G labels t x r) :
    (actualNodeEquiv G labels t x r a).val = nodeHistory G labels r a.val := rfl

@[simp] theorem actualNodeEquiv_symm_val (r : Nat) (a : Node (history G labels t x) r) :
    nodeHistory G labels r ((actualNodeEquiv G labels t x r).symm a).val = a.val :=
  congrArg Subtype.val ((actualNodeEquiv G labels t x r).apply_symm_apply a)

@[simp] theorem actualNodeEquiv_observer : actualNodeEquiv G labels t x t (observerNode G labels t x) =
    ⟨history G labels t x, self_mem_levels t _⟩ := by
  apply Subtype.ext
  exact nodeHistory_classOf G labels t x

/-- Isomorphism of actual visible history-tree nodes. It preserves only
the information visible to the observer, including the distinguished node. -/
structure ActualIso where
  equiv : ∀ r, ActualNode G labels t x r ≃ ActualNode H labels' t y r
  input : ∀ r (a : ActualNode G labels t x r),
    PaperHistory.label H labels' r (equiv r a).val = PaperHistory.label G labels r a.val
  degree : ∀ r (b : ActualNode G labels t x (r + 1)),
    PaperHistory.outdegreeLabel H labels' r (equiv (r + 1) b).val = PaperHistory.outdegreeLabel G labels r b.val
  parent : ∀ r (a : ActualNode G labels t x r) (b : ActualNode G labels t x (r + 1)),
    PaperHistory.parent G labels r b.val = a.val ↔
      PaperHistory.parent H labels' r (equiv (r + 1) b).val = (equiv r a).val
  red : ∀ r (a : ActualNode G labels t x r) (b : ActualNode G labels t x (r + 1)),
    PaperHistory.redMultiplicity H labels' r (equiv r a).val (equiv (r + 1) b).val =
      PaperHistory.redMultiplicity G labels r a.val b.val
  pointed : (equiv t (observerNode G labels t x)).val = PaperHistory.classOf H labels' t y

noncomputable def Iso.actualEquiv (I : Iso (history G labels t x) (history H labels' t y)) (r : Nat) :
    ActualNode G labels t x r ≃ ActualNode H labels' t y r :=
  (actualNodeEquiv G labels t x r).trans ((I.equiv r).trans (actualNodeEquiv H labels' t y r).symm)

theorem Iso.actualEquiv_history (I : Iso (history G labels t x) (history H labels' t y))
    (r : Nat) (a : ActualNode G labels t x r) :
    nodeHistory H labels' r ((I.actualEquiv G H labels labels' t x y r) a).val =
      (I.equiv r (actualNodeEquiv G labels t x r a)).val :=
  actualNodeEquiv_symm_val H labels' t y r _

/-- Canonical vista isomorphisms transport to actual quotient-node vistas. -/
noncomputable def Iso.toActual (I : Iso (history G labels t x) (history H labels' t y)) :
    ActualIso G H labels labels' t x y where
  equiv := I.actualEquiv G H labels labels' t x y
  input := by
    intro r a
    have h := I.input r (actualNodeEquiv G labels t x r a)
    rw [← I.actualEquiv_history G H labels labels' t x y r a] at h
    simpa only [actualNodeEquiv_val, nodeHistory_input] using h
  degree := by
    intro r b
    have h := I.degree r (actualNodeEquiv G labels t x (r + 1) b)
    rw [← I.actualEquiv_history G H labels labels' t x y (r + 1) b] at h
    simpa only [actualNodeEquiv_val, nodeHistory_degree] using h
  parent := by
    intro r a b
    have h := I.parent r (actualNodeEquiv G labels t x r a) (actualNodeEquiv G labels t x (r + 1) b)
    rw [← I.actualEquiv_history G H labels labels' t x y r a,
      ← I.actualEquiv_history G H labels labels' t x y (r + 1) b] at h
    simpa only [actualNodeEquiv_val, nodeHistory_parent,
      (nodeHistory_injective G labels r).eq_iff, (nodeHistory_injective H labels' r).eq_iff] using h
  red := by
    intro r a b
    have h := I.red r (actualNodeEquiv G labels t x r a) (actualNodeEquiv G labels t x (r + 1) b)
    rw [← I.actualEquiv_history G H labels labels' t x y r a,
      ← I.actualEquiv_history G H labels labels' t x y (r + 1) b] at h
    simpa only [actualNodeEquiv_val, nodeHistory_red] using h
  pointed := by
    apply nodeHistory_injective H labels' t
    rw [I.actualEquiv_history G H labels labels' t x y, actualNodeEquiv_observer,
      nodeHistory_classOf]
    exact I.pointed

noncomputable def ActualIso.canonicalEquiv (I : ActualIso G H labels labels' t x y) (r : Nat) :
    Node (history G labels t x) r ≃ Node (history H labels' t y) r :=
  (actualNodeEquiv G labels t x r).symm.trans ((I.equiv r).trans (actualNodeEquiv H labels' t y r))

theorem ActualIso.canonicalEquiv_val (I : ActualIso G H labels labels' t x y)
    (r : Nat) (a : Node (history G labels t x) r) :
    (I.canonicalEquiv G H labels labels' t x y r a).val =
      nodeHistory H labels' r (I.equiv r ((actualNodeEquiv G labels t x r).symm a)).val := rfl

/-- Actual history-tree isomorphisms transport back to the intrinsic vista. -/
noncomputable def ActualIso.toCanonical (I : ActualIso G H labels labels' t x y) :
    Iso (history G labels t x) (history H labels' t y) where
  equiv := I.canonicalEquiv G H labels labels' t x y
  input := by
    intro r a
    rw [I.canonicalEquiv_val, nodeHistory_input, I.input, ← nodeHistory_input,
      actualNodeEquiv_symm_val]
  degree := by
    intro r b
    rw [I.canonicalEquiv_val, nodeHistory_degree, I.degree, ← nodeHistory_degree,
      actualNodeEquiv_symm_val]
  parent := by
    intro r a b
    have h := I.parent r ((actualNodeEquiv G labels t x r).symm a)
      ((actualNodeEquiv G labels t x (r + 1)).symm b)
    rw [← (nodeHistory_injective G labels r).eq_iff,
      ← (nodeHistory_injective H labels' r).eq_iff,
      ← nodeHistory_parent, ← nodeHistory_parent,
      actualNodeEquiv_symm_val, actualNodeEquiv_symm_val] at h
    exact h
  red := by
    intro r a b
    rw [I.canonicalEquiv_val, I.canonicalEquiv_val, nodeHistory_red, I.red,
      ← nodeHistory_red, actualNodeEquiv_symm_val, actualNodeEquiv_symm_val]
  pointed := by
    rw [I.canonicalEquiv_val]
    have obs := (actualNodeEquiv G labels t x t).symm_apply_apply (observerNode G labels t x)
    rw [actualNodeEquiv_observer] at obs
    rw [obs, I.pointed, nodeHistory_classOf]

/-- Exact cross-population correspondence with vistas of the quotient
history trees, not merely with an executable DAG encoding. -/
theorem actual_history_eq_iff_actualIso :
    history G labels t x = history H labels' t y ↔ Nonempty (ActualIso G H labels labels' t x y) := by
  constructor
  · intro eq
    obtain ⟨I⟩ := (eq_iff_nonempty_iso _ _).mp eq
    exact ⟨I.toActual G H labels labels' t x y⟩
  · rintro ⟨I⟩
    exact (I.toCanonical G H labels labels' t x y).history_eq

/-- Isomorphic actual vistas determine the same protocol state and terminal
decision, including the recursive removal of silently halted senders. -/
theorem ActualIso.same_protocol_status (I : ActualIso G H labels labels' t x y)
    {State : Type} (P : Protocol State) (ell : Nat) :
    P.trace ell G labels t x = P.trace ell H labels' t y :=
  P.same_history_same_status ell G H labels labels' t x y
    ((I.toCanonical G H labels labels' t x y).history_eq)

end Counting.VistaIsomorphism
