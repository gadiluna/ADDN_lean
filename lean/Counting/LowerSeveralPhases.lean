import Counting.LowerSeveralRelay

/-! The two middle phases, with the exact relay replacement on both sides. -/

namespace Counting.LowerSeveralPhases
open DirectedCounting
open scoped BigOperators

abbrev Leaders (k : Nat) := Fin (k + 2)
abbrev Small (k g : Nat) := LowerSeveralRelay.Vertex (Leaders k) Unit g
abbrev Large (k g : Nat) := LowerSeveralRelay.Vertex (Leaders k) (Leaders k) g

def observer (k : Nat) : Leaders k := Fin.last (k + 1)

def smallLeader (k g : Nat) (l : Leaders k) : Small k g := .inl (.inl l)
def smallNonleader (k g : Nat) : Small k g := .inl (.inr ())
def largeLeader (k g : Nat) (l : Leaders k) : Large k g := .inl (.inl l)
def largeNonleader (k g : Nat) (n : Leaders k) : Large k g := .inl (.inr n)

/-- One full-information update, also used from arbitrary phase-start states. -/
noncomputable def step {V A : Type} [Fintype V]
    (edge : V → V → Nat) (state : V → A) (v : V) : A × Nat × Multiset A :=
  (state v, ∑ w, edge v w, incoming edge state v)

/-- Transport a graph through an explicit equivalence of agent sets. -/
def relabel {V W : Type} (e : V ≃ W) (edge : W → W → Nat) (u v : V) : Nat :=
  edge (e u) (e v)

theorem relabel_degree {V W : Type} [Fintype V] [Fintype W]
    (e : V ≃ W) (edge : W → W → Nat) (u : V) :
    (∑ v, relabel e edge u v) = ∑ w, edge (e u) w :=
  Fintype.sum_equiv e _ _ (fun _ ↦ rfl)

theorem relabel_incoming {V W A : Type} [Fintype V] [Fintype W]
    (e : V ≃ W) (edge : W → W → Nat) (state : V → A) (v : V) :
    incoming (relabel e edge) state v = incoming edge (fun w ↦ state (e.symm w)) (e v) := by
  unfold incoming
  exact Fintype.sum_equiv e _ _ (fun u ↦ by simp [relabel])

theorem relabel_connected {V W : Type} (e : V ≃ W) (edge : W → W → Nat)
    (connected : StronglyConnected (fun u v ↦ 0 < edge u v)) :
    StronglyConnected (fun u v ↦ 0 < relabel e edge u v) := by
  intro u v
  have h := Relation.ReflTransGen.lift e.symm
    (show (fun u v ↦ 0 < edge u v) ≤
      Function.onFun (fun u v ↦ 0 < relabel e edge u v) e.symm by
      intro u v h
      simpa [relabel, Function.onFun] using h) _ _ (connected (e u) (e v))
  simpa [Function.onFun] using h

/-- Unit bidirected star centered at the sole original nonleader. -/
def star (k : Nat) : (Leaders k ⊕ Unit) → (Leaders k ⊕ Unit) → Nat
  | .inl _, .inr _ => 1
  | .inr _, .inl _ => 1
  | _, _ => 0

theorem star_connected (k : Nat) : StronglyConnected (fun u v ↦ 0 < star k u v) := by
  intro u v
  have hy (u : Leaders k ⊕ Unit) : Relation.ReflTransGen (fun u v ↦ 0 < star k u v) u (.inr ()) := by
    cases u with
    | inl _ => exact .single (by simp [star])
    | inr n => cases n; exact .refl
  have hx (v : Leaders k ⊕ Unit) : Relation.ReflTransGen (fun u v ↦ 0 < star k u v) (.inr ()) v := by
    cases v with
    | inl _ => exact .single (by simp [star])
    | inr n => cases n; exact .refl
  exact (hy u).trans (hx v)

theorem star_leader_degree (k : Nat) (l : Leaders k) : (∑v, star k (.inl l) v) = 1 := by
  rw [Fintype.sum_sum_type]
  simp [star]

theorem star_nonleader_degree (k : Nat) : (∑v, star k (.inr ()) v) = k + 2 := by
  rw [Fintype.sum_sum_type]
  simp [star]

theorem star_nonleader_incoming {A : Type} (k : Nat) (state : Leaders k ⊕ Unit → A)
    (common : A) (uniform : ∀ l, state (.inl l) = common) :
    incoming (star k) state (.inr ()) = Multiset.replicate (k + 2) common := by
  unfold incoming
  rw [Fintype.sum_sum_type]
  simp [star, uniform, Multiset.nsmul_singleton]

def firstSmallCore (k : Nat) := star k
def firstLargeCore (k : Nat) (i : Leaders k) := TwoCenter.edge i (observer k) (k + 2)
def secondSmallCore (k : Nat) (i : Leaders k) := TwoCenter.edge i () 1
def secondLargeCore (k : Nat) (i : Leaders k) :=
  relabel (Equiv.sumComm (Leaders k) (Leaders k)) (TwoCenter.edge i (observer k) 1)

def firstSmall (k g : Nat) := LowerSeveralRelay.edge (firstSmallCore k) () g
def firstLarge (k g : Nat) (i : Leaders k) :=
  LowerSeveralRelay.edge (firstLargeCore k i) (observer k) g

def secondSmall (k g : Nat) (i : Leaders k) := LowerSeveralRelay.edge (secondSmallCore k i) () g
def secondLarge (k g : Nat) (i : Leaders k) := LowerSeveralRelay.edge (secondLargeCore k i) i g

@[simp] theorem firstSmall_fanout (k : Nat) (l : Leaders k) : firstSmallCore k (.inr ()) (.inl l) = 1 := rfl
@[simp] theorem firstLarge_fanout (k : Nat) (i l : Leaders k) :
    firstLargeCore k i (.inr (observer k)) (.inl l) = 1 := by simp [firstLargeCore, TwoCenter.edge]
@[simp] theorem secondSmall_fanout (k : Nat) (i l : Leaders k) :
    secondSmallCore k i (.inr ()) (.inl l) = 1 := by simp [secondSmallCore, TwoCenter.edge]
@[simp] theorem secondLarge_fanout (k : Nat) (i l : Leaders k) :
    secondLargeCore k i (.inr i) (.inl l) = 1 := by simp [secondLargeCore, relabel, TwoCenter.edge]

theorem firstSmall_degree (k g : Nat) (l : Leaders k) :
    (∑v, firstSmall k g (smallLeader k g l) v) = 1 := by
  dsimp only [firstSmall, smallLeader]
  rw [LowerSeveralRelay.core_outdegree _ _ _ (firstSmall_fanout k)]
  exact star_leader_degree k l

theorem firstLarge_degree (k g : Nat) (i l : Leaders k) (different : l ≠ i) :
    (∑v, firstLarge k g i (largeLeader k g l) v) = 1 := by
  dsimp only [firstLarge, largeLeader]
  rw [LowerSeveralRelay.core_outdegree _ _ _ (firstLarge_fanout k i)]
  simpa [firstLargeCore] using TwoCenter.left_outdegree i (observer k) (k + 2) l different

theorem firstSmall_nonleader_degree (k g : Nat) :
    (∑v, firstSmall k g (smallNonleader k g) v) = k + 2 := by
  dsimp only [firstSmall, smallNonleader]
  rw [LowerSeveralRelay.core_outdegree _ _ _ (firstSmall_fanout k)]
  exact star_nonleader_degree k

theorem firstLarge_nonleader_degree (k g : Nat) (i n : Leaders k) :
    (∑v, firstLarge k g i (largeNonleader k g n) v) = k + 2 := by
  dsimp only [firstLarge, largeNonleader]
  rw [LowerSeveralRelay.core_outdegree _ _ _ (firstLarge_fanout k i)]
  simpa [firstLargeCore, Leaders] using TwoCenter.right_outdegree i (observer k) (k + 2) n

theorem secondSmall_degree (k g : Nat) (i l : Leaders k) (different : l ≠ i) :
    (∑v, secondSmall k g i (smallLeader k g l) v) = k + 2 := by
  dsimp only [secondSmall, smallLeader]
  rw [LowerSeveralRelay.core_outdegree _ _ _ (secondSmall_fanout k i)]
  simpa [secondSmallCore] using TwoCenter.left_outdegree i () 1 l different

theorem secondLarge_degree (k g : Nat) (i l : Leaders k) :
    (∑v, secondLarge k g i (largeLeader k g l) v) = k + 2 := by
  dsimp only [secondLarge, largeLeader]
  rw [LowerSeveralRelay.core_outdegree _ _ _ (secondLarge_fanout k i), secondLargeCore, relabel_degree]
  simpa [Leaders] using TwoCenter.right_outdegree i (observer k) 1 l

theorem secondSmall_nonleader_degree (k g : Nat) (i : Leaders k) :
    (∑v, secondSmall k g i (smallNonleader k g) v) = k + 2 := by
  dsimp only [secondSmall, smallNonleader]
  rw [LowerSeveralRelay.core_outdegree _ _ _ (secondSmall_fanout k i)]
  simpa [secondSmallCore, Leaders] using TwoCenter.right_outdegree i () 1 ()

theorem secondLarge_nonleader_degree (k g : Nat) (i n : Leaders k) (different : n ≠ i) :
    (∑v, secondLarge k g i (largeNonleader k g n) v) = k + 2 := by
  dsimp only [secondLarge, largeNonleader]
  rw [LowerSeveralRelay.core_outdegree _ _ _ (secondLarge_fanout k i), secondLargeCore, relabel_degree]
  simpa using TwoCenter.left_outdegree i (observer k) 1 n different

/-- Generic equality of leader-source states across corresponding relay paths. -/
theorem leaderSource_match {N N' A : Type} (k g : Nat)
    (a : LowerSeveralRelay.Vertex (Leaders k) N g → A)
    (b : LowerSeveralRelay.Vertex (Leaders k) N' g → A) (n : N) (n' : N')
    (centers : a (.inl (.inr n)) = b (.inl (.inr n')))
    (relays : ∀ j, a (.inr j) = b (.inr j)) :
    a (LowerSeveralRelay.leaderSource n g) = b (LowerSeveralRelay.leaderSource n' g) := by
  unfold LowerSeveralRelay.leaderSource
  split_ifs
  · exact relays _
  · exact centers

/-- Generic equality of each relay's predecessor state. -/
theorem relaySource_match {N N' A : Type} (k g : Nat)
    (a : LowerSeveralRelay.Vertex (Leaders k) N g → A)
    (b : LowerSeveralRelay.Vertex (Leaders k) N' g → A) (n : N) (n' : N')
    (centers : a (.inl (.inr n)) = b (.inl (.inr n')))
    (relays : ∀ j, a (.inr j) = b (.inr j)) (j : Fin g) :
    a (LowerSeveralRelay.relaySource n g j) = b (LowerSeveralRelay.relaySource n' g j) := by
  unfold LowerSeveralRelay.relaySource
  split_ifs
  · exact centers
  · exact relays _

/-- First-phase leader observations in the smaller graph. -/
theorem firstSmall_leader_step {A : Type} (k g : Nat) (state : Small k g → A) (l : Leaders k) :
    step (firstSmall k g) state (smallLeader k g l) =
      (state (smallLeader k g l), 1, {state (LowerSeveralRelay.leaderSource () g)}) := by
  dsimp only [step]
  refine Prod.ext rfl ?_
  apply Prod.ext (firstSmall_degree k g l)
  dsimp only [firstSmall, smallLeader]
  apply LowerSeveralRelay.leader_incoming
  intro u
  cases u with
  | inl u => simp [firstSmallCore, star]
  | inr u => cases u; simp [firstSmallCore, star]

/-- Unselected large leaders receive the same observations. -/
theorem firstLarge_leader_step {A : Type} (k g : Nat) (state : Large k g → A)
    (i l : Leaders k) (different : l ≠ i) :
    step (firstLarge k g i) state (largeLeader k g l) =
      (state (largeLeader k g l), 1, {state (LowerSeveralRelay.leaderSource (observer k) g)}) := by
  dsimp only [step]
  refine Prod.ext rfl ?_
  apply Prod.ext (firstLarge_degree k g i l different)
  dsimp only [firstLarge, largeLeader]
  apply LowerSeveralRelay.leader_incoming
  intro u
  cases u <;> simp [firstLargeCore, TwoCenter.edge, different]

/-- Every original nonleader in the large first-phase graph hears ell copies
of the newly selected leader's previous state. -/
theorem firstLarge_nonleader_step {A : Type} (k g : Nat) (state : Large k g → A)
    (i n : Leaders k) :
    step (firstLarge k g i) state (largeNonleader k g n) =
      (state (largeNonleader k g n), k + 2,
        Multiset.replicate (k + 2) (state (largeLeader k g i))) := by
  dsimp only [step]
  refine Prod.ext rfl ?_
  apply Prod.ext (firstLarge_nonleader_degree k g i n)
  dsimp only [firstLarge, largeNonleader]
  rw [LowerSeveralRelay.nonleader_incoming]
  exact TwoCenter.right_incoming i (observer k) (k + 2) _ n

/-- The small star supplies ell copies by distinct matching senders. -/
theorem firstSmall_nonleader_step {A : Type} (k g : Nat) (state : Small k g → A)
    (common : A) (uniform : ∀ l, state (smallLeader k g l) = common) :
    step (firstSmall k g) state (smallNonleader k g) =
      (state (smallNonleader k g), k + 2, Multiset.replicate (k + 2) common) := by
  dsimp only [step]
  refine Prod.ext rfl ?_
  apply Prod.ext (firstSmall_nonleader_degree k g)
  dsimp only [firstSmall, smallNonleader]
  rw [LowerSeveralRelay.nonleader_incoming]
  exact star_nonleader_incoming k _ common uniform

/-- Ordinary small leaders in the second phase hear the original nonleader
through the relay path and have degree ell. -/
theorem secondSmall_leader_step {A : Type} (k g : Nat) (state : Small k g → A)
    (i l : Leaders k) (different : l ≠ i) :
    step (secondSmall k g i) state (smallLeader k g l) =
      (state (smallLeader k g l), k + 2, {state (LowerSeveralRelay.leaderSource () g)}) := by
  dsimp only [step]
  refine Prod.ext rfl ?_
  apply Prod.ext (secondSmall_degree k g i l different)
  dsimp only [secondSmall, smallLeader]
  apply LowerSeveralRelay.leader_incoming
  intro u
  cases u with
  | inl u => simp [secondSmallCore, TwoCenter.edge, different]
  | inr u => cases u; simp [secondSmallCore, TwoCenter.edge]

/-- Every large leader receives the selected nonleader through the same relay path. -/
theorem secondLarge_leader_step {A : Type} (k g : Nat) (state : Large k g → A)
    (i l : Leaders k) :
    step (secondLarge k g i) state (largeLeader k g l) =
      (state (largeLeader k g l), k + 2, {state (LowerSeveralRelay.leaderSource i g)}) := by
  dsimp only [step]
  refine Prod.ext rfl ?_
  apply Prod.ext (secondLarge_degree k g i l)
  dsimp only [secondLarge, largeLeader]
  apply LowerSeveralRelay.leader_incoming
  intro u
  cases u <;> simp [secondLargeCore, relabel, TwoCenter.edge]

/-- The sole small original nonleader hears the currently selected small leader. -/
theorem secondSmall_nonleader_step {A : Type} (k g : Nat) (state : Small k g → A)
    (i : Leaders k) :
    step (secondSmall k g i) state (smallNonleader k g) =
      (state (smallNonleader k g), k + 2, {state (smallLeader k g i)}) := by
  dsimp only [step]
  refine Prod.ext rfl ?_
  apply Prod.ext (secondSmall_nonleader_degree k g i)
  dsimp only [secondSmall, smallNonleader]
  rw [LowerSeveralRelay.nonleader_incoming]
  simpa [secondSmallCore, smallLeader] using TwoCenter.right_incoming i () 1 (fun u ↦ state (.inl u)) ()

/-- Unselected large nonleaders hear the designated large observer. -/
theorem secondLarge_nonleader_step {A : Type} (k g : Nat) (state : Large k g → A)
    (i n : Leaders k) (different : n ≠ i) :
    step (secondLarge k g i) state (largeNonleader k g n) =
      (state (largeNonleader k g n), k + 2, {state (largeLeader k g (observer k))}) := by
  dsimp only [step]
  refine Prod.ext rfl ?_
  apply Prod.ext (secondLarge_nonleader_degree k g i n different)
  dsimp only [secondLarge, largeNonleader]
  rw [LowerSeveralRelay.nonleader_incoming]
  unfold secondLargeCore
  rw [relabel_incoming]
  exact TwoCenter.left_incoming i (observer k) 1 _ n different

/-- Equal source and relay states give equal next relay observations, even
if the two underlying cores differ. -/
theorem relay_step_match {N N' A : Type} [Fintype N] [Fintype N'] [DecidableEq N] [DecidableEq N']
    (k g : Nat) (core : (Leaders k ⊕ N) → (Leaders k ⊕ N) → Nat)
    (core' : (Leaders k ⊕ N') → (Leaders k ⊕ N') → Nat)
    (center : N) (center' : N')
    (a : LowerSeveralRelay.Vertex (Leaders k) N g → A)
    (b : LowerSeveralRelay.Vertex (Leaders k) N' g → A)
    (centers : a (.inl (.inr center)) = b (.inl (.inr center')))
    (relays : ∀ j, a (.inr j) = b (.inr j)) (j : Fin g) :
    step (LowerSeveralRelay.edge core center g) a (.inr j) =
      step (LowerSeveralRelay.edge core' center' g) b (.inr j) := by
  dsimp only [step]
  apply Prod.ext (relays j)
  apply Prod.ext
  · rw [LowerSeveralRelay.relay_outdegree, LowerSeveralRelay.relay_outdegree]
  · rw [LowerSeveralRelay.relay_incoming, LowerSeveralRelay.relay_incoming,
      relaySource_match k g a b center center' centers relays j]

/-- The first-phase invariant, including every corresponding relay pair. -/
structure FirstMatched {A : Type} (k g t : Nat) (a : Small k g → A) (b : Large k g → A) : Prop where
  small_leaders : ∀ l, a (smallLeader k g l) = a (smallLeader k g (observer k))
  leaders : ∀ l, t ≤ l.val → a (smallLeader k g (observer k)) = b (largeLeader k g l)
  nonleaders : ∀ n, a (smallNonleader k g) = b (largeNonleader k g n)
  relays : ∀ j, a (.inr j) = b (.inr j)

/-- The second phase retains the unselected leaders on the smaller side and
unselected nonleaders on the larger side. -/
structure SecondMatched {A : Type} (k g t : Nat) (a : Small k g → A) (b : Large k g → A) : Prop where
  leaders : ∀ l, t ≤ l.val → a (smallLeader k g l) = b (largeLeader k g (observer k))
  nonleaders : ∀ n, t ≤ n.val → a (smallNonleader k g) = b (largeNonleader k g n)
  relays : ∀ j, a (.inr j) = b (.inr j)

/-- A first-phase round consumes the matching old state of its new center;
its newly learned outdegree cannot change the state that was just sent. -/
theorem first_step_preserves {A : Type} (k g : Nat) (i : Leaders k)
    (a : Small k g → A) (b : Large k g → A) (h : FirstMatched k g i.val a b) :
    FirstMatched k g (i.val + 1) (step (firstSmall k g) a) (step (firstLarge k g i) b) := by
  have hsource := leaderSource_match k g a b () (observer k) (h.nonleaders (observer k)) h.relays
  constructor
  · intro l
    rw [firstSmall_leader_step, firstSmall_leader_step, h.small_leaders l]
  · intro l hl
    have hne : l ≠ i := by intro heq; subst l; omega
    rw [firstSmall_leader_step, firstLarge_leader_step k g b i l hne,
      h.leaders l (by omega), hsource]
  · intro n
    rw [firstSmall_nonleader_step k g a _ h.small_leaders, firstLarge_nonleader_step,
      h.nonleaders n, h.leaders i le_rfl]
  · intro j
    exact relay_step_match k g _ _ () (observer k) a b (h.nonleaders (observer k)) h.relays j

/-- The final first-phase state establishes the second-phase invariant. -/
theorem first_to_second {A : Type} (k g : Nat) (a : Small k g → A) (b : Large k g → A)
    (h : FirstMatched k g (k + 1) a b) : SecondMatched k g 0 a b := by
  constructor
  · intro l _
    exact (h.small_leaders l).trans (h.leaders (observer k) (by simp [observer]))
  · intro n _
    exact h.nonleaders n
  · exact h.relays

/-- One second-phase round consumes one matching small leader and one
matching large nonleader while preserving the remaining comparisons. -/
theorem second_step_preserves {A : Type} (k g : Nat) (i : Leaders k)
    (a : Small k g → A) (b : Large k g → A) (h : SecondMatched k g i.val a b) :
    SecondMatched k g (i.val + 1) (step (secondSmall k g i) a) (step (secondLarge k g i) b) := by
  have hsource := leaderSource_match k g a b () i (h.nonleaders i le_rfl) h.relays
  constructor
  · intro l hl
    have hne : l ≠ i := by intro heq; subst l; omega
    rw [secondSmall_leader_step k g a i l hne, secondLarge_leader_step,
      h.leaders l (by omega), hsource]
  · intro n hn
    have hne : n ≠ i := by intro heq; subst n; omega
    rw [secondSmall_nonleader_step, secondLarge_nonleader_step k g b i n hne,
      h.nonleaders n (by omega), h.leaders i le_rfl]
  · intro j
    exact relay_step_match k g _ _ () i a b (h.nonleaders i le_rfl) h.relays j

/-- The two observers, final original nonleaders and every relay match at
the end of the second phase. -/
theorem second_final_matches {A : Type} (k g : Nat) (a : Small k g → A) (b : Large k g → A)
    (h : SecondMatched k g (k + 1) a b) :
    a (smallLeader k g (observer k)) = b (largeLeader k g (observer k)) ∧
      a (smallNonleader k g) = b (largeNonleader k g (observer k)) ∧
      ∀ j, a (.inr j) = b (.inr j) :=
  ⟨h.leaders _ (by simp [observer]), h.nonleaders _ (by simp [observer]), h.relays⟩

/-- With no preliminary delay, the input labels establish the first invariant. -/
theorem initial_matches (k g : Nat) :
    FirstMatched k g 0 (LowerSeveralRelay.leader (L := Leaders k) (N := Unit))
      (LowerSeveralRelay.leader (L := Leaders k) (N := Leaders k)) where
  small_leaders := fun _ ↦ rfl
  leaders := fun _ _ ↦ rfl
  nonleaders := fun _ ↦ rfl
  relays := fun _ ↦ rfl

end Counting.LowerSeveralPhases
