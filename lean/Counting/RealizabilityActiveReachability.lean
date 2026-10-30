import Counting.RealizabilityVerifierGraph

namespace Counting.RealizabilityVerifier

/-- A fixed carrier with inactive slots. Iteration is bounded by the explicit
carrier cardinality, never by a binary population count. -/
def activeConnectedCheck {V : Type*} [Fintype V] [DecidableEq V]
    (active : V → Bool) (arc : V → V → Bool) : Bool :=
  decide (∀ source, active source = true → ∀ target, active target = true →
    target ∈ reachable arc source (Fintype.card V))

theorem reachable_active {V : Type*} [Fintype V] [DecidableEq V]
    (active : V → Bool) (arc : V → V → Bool)
    (closed : ∀ x y, arc x y = true → active y = true)
    (source : V) (initial : active source = true) (k : Nat) :
    ∀ target ∈ reachable arc source k, active target = true := by
  induction k with
  | zero =>
    intro target member
    have same : target = source := by simpa [reachable] using member
    simpa only [same] using initial
  | succ k ih =>
    intro target member
    rcases (mem_reachStep _ _ _).mp member with old | ⟨previous,_,edge⟩
    · exact ih target old
    · exact closed previous target edge

theorem reachable_subtype_iff {V : Type*} [Fintype V] [DecidableEq V]
    (active : V → Bool) (arc : V → V → Bool)
    (closed : ∀ x y, arc x y = true → active y = true)
    (source : {v : V // active v = true}) (k : Nat) :
    ∀ target : {v : V // active v = true},
      target.val ∈ reachable arc source.val k ↔
        target ∈ reachable (fun x y : {v : V // active v = true} => arc x.val y.val) source k := by
  induction k with
  | zero => intro target; simp [reachable,Subtype.ext_iff]
  | succ k ih =>
    intro target
    simp only [reachable,mem_reachStep]
    constructor
    · rintro (old | ⟨previous,member,edge⟩)
      · exact Or.inl ((ih target).mp old)
      · have present := reachable_active active arc closed source.val source.property k previous member
        exact Or.inr ⟨⟨previous,present⟩,(ih ⟨previous,present⟩).mp member,edge⟩
    · rintro (old | ⟨previous,member,edge⟩)
      · exact Or.inl ((ih target).mpr old)
      · exact Or.inr ⟨previous.val,(ih previous).mpr member,edge⟩

theorem activeConnectedCheck_iff {V : Type*} [Fintype V] [DecidableEq V]
    (active : V → Bool) (arc : V → V → Bool)
    (closed : ∀ x y, arc x y = true → active y = true) :
    activeConnectedCheck active arc = true ↔
      DirectedCounting.StronglyConnected (fun x y : {v : V // active v = true} => arc x.val y.val = true) := by
  simp only [activeConnectedCheck,decide_eq_true_eq]
  constructor
  · intro accepted source target
    apply reachable_sound (fun x y : {v : V // active v = true} => arc x.val y.val) source
      (Fintype.card V) target
    exact (reachable_subtype_iff active arc closed source (Fintype.card V) target).mp
      (accepted source.val source.property target.val target.property)
  · intro connected source sourceActive target targetActive
    let start : {v : V // active v = true} := ⟨source,sourceActive⟩
    let finish : {v : V // active v = true} := ⟨target,targetActive⟩
    apply (reachable_subtype_iff active arc closed start (Fintype.card V) finish).mpr
    apply reachable_mono _ start (Fintype.card_subtype_le (fun v : V => active v = true))
    rw [reachable_complete _ connected start]
    exact Finset.mem_univ finish

end Counting.RealizabilityVerifier
