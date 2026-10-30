import Counting.TwoCenter

/-!
# Relay replacement for the several-leader lower bound

A core consists of a leader summand L and a nonleader summand N. The chosen
nonleader sends one arc to every leader. The extension replaces that fanout
by an ell-arc relay path followed by the same unit fanout. The replacement
preserves every original outdegree.
-/

namespace Counting.LowerSeveralRelay

open DirectedCounting
open scoped BigOperators

abbrev Core (L N : Type) := L ⊕ N
abbrev Vertex (L N : Type) (g : Nat) := Core L N ⊕ Fin g

variable {L N : Type} [Fintype L] [Fintype N] [DecidableEq L] [DecidableEq N]

/-- Core arcs retained after replacing the selected fanout. -/
def retained (core : Core L N → Core L N → Nat) (center : N) (g : Nat) :
    Core L N → Core L N → Nat
  | .inr n, .inl l => if n = center ∧ 0 < g then 0 else core (.inr n) (.inl l)
  | u, v => core u v

/-- The exact relay extension, including the unchanged core when g=0. -/
def edge (core : Core L N → Core L N → Nat) (center : N) (g : Nat) :
    Vertex L N g → Vertex L N g → Nat
  | .inl u, .inl v => retained core center g u v
  | .inl u, .inr j => if u = .inr center ∧ j.val = 0 then Fintype.card L else 0
  | .inr i, .inl (.inl _) => if i.val + 1 = g then 1 else 0
  | .inr _, .inl (.inr _) => 0
  | .inr i, .inr j => if i.val + 1 = j.val then Fintype.card L else 0

def leader : Vertex L N g → Bool
  | .inl (.inl _) => true
  | _ => false

omit [Fintype L] [Fintype N] [DecidableEq L] in
@[simp] theorem retained_zero (core : Core L N → Core L N → Nat) (center : N)
    (u v : Core L N) : retained core center 0 u v = core u v := by
  cases u <;> cases v <;> simp [retained]

omit [Fintype L] [Fintype N] [DecidableEq L] in
@[simp] theorem retained_nonleader (core : Core L N → Core L N → Nat) (center : N)
    (g : Nat) (u : Core L N) (v : N) :
    retained core center g u (.inr v) = core u (.inr v) := by
  cases u <;> rfl

omit [Fintype N] in
/-- Core looplessness is preserved; all newly added arcs have distinct endpoints. -/
theorem loopless (core : Core L N → Core L N → Nat) (center : N) (g : Nat)
    (hcore : ∀ u, core u u = 0) (u : Vertex L N g) : edge core center g u u = 0 := by
  cases u with
  | inl u => cases u <;> simpa [edge, retained] using hcore _
  | inr i => simp [edge]

omit [Fintype N] in
/-- Multiplicities remain bounded by ell when this was true in the core. -/
theorem multiplicity_le (core : Core L N → Core L N → Nat) (center : N) (g : Nat)
    (positive : 0 < Fintype.card L) (hcore : ∀ u v, core u v ≤ Fintype.card L)
    (u v : Vertex L N g) : edge core center g u v ≤ Fintype.card L := by
  cases u with
  | inl u =>
      cases v with
      | inl v =>
          cases u <;> cases v <;> dsimp only [edge, retained] <;>
            (try split_ifs) <;> first | exact hcore _ _ | omega
      | inr j => simp only [edge]; split_ifs <;> omega
  | inr i =>
      cases v with
      | inl v => cases v <;> simp only [edge] <;> (try split_ifs) <;> omega
      | inr j => simp only [edge]; split_ifs <;> omega

/-- There is exactly one first relay when the path is nonempty. -/
theorem sum_first (g : Nat) (A : Nat) :
    (∑ j : Fin g, if j.val = 0 then A else 0) = if 0 < g then A else 0 := by
  by_cases hg : 0 < g
  · let first : Fin g := ⟨0, hg⟩
    have heq : ∀ j : Fin g, j.val = 0 ↔ j = first := fun j ↦ by simp [Fin.ext_iff, first]
    simp only [heq]
    simp [hg]
  · have hg0 : g = 0 := by omega
    subst g
    simp

/-- Original outdegrees are unchanged by replacement of the unit fanout. -/
theorem core_outdegree (core : Core L N → Core L N → Nat) (center : N) (g : Nat)
    (fanout : ∀ l, core (.inr center) (.inl l) = 1) (u : Core L N) :
    (∑ v, edge core center g (.inl u) v) = ∑ v, core u v := by
  rw [Fintype.sum_sum_type]
  cases u with
  | inl l =>
      simp only [edge, retained, Sum.inl_ne_inr, false_and, if_false,
        Finset.sum_const_zero, add_zero]
  | inr n =>
      by_cases hn : n = center
      · subst n
        rw [Fintype.sum_sum_type, Fintype.sum_sum_type]
        simp only [edge, retained, true_and, fanout]
        rw [sum_first]
        by_cases hg : 0 < g <;> simp [hg, Nat.add_comm]
      · rw [Fintype.sum_sum_type, Fintype.sum_sum_type]
        simp [edge, retained, hn]

/-- A relay's outgoing chain or terminal fanout has exactly ell arcs. -/
theorem relay_outdegree (core : Core L N → Core L N → Nat) (center : N)
    (g : Nat) (i : Fin g) :
    (∑ v, edge core center g (.inr i) v) = Fintype.card L := by
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type]
  simp only [edge, Finset.sum_const_zero, add_zero]
  by_cases hlast : i.val + 1 = g
  · have hnone : ∀ j : Fin g, ¬ i.val + 1 = j.val := fun j ↦ by omega
    simp only [hnone, if_false, Finset.sum_const_zero, add_zero]
    simp [hlast]
  · have hnext : i.val + 1 < g := by omega
    let next : Fin g := ⟨i.val + 1, hnext⟩
    have heq : ∀ j : Fin g, i.val + 1 = j.val ↔ j = next := fun j ↦ by
      simp only [Fin.ext_iff, next]
      omega
    simp [hlast, heq]

/-- Relays do not change the messages received by an original nonleader. -/
theorem nonleader_incoming {A : Type} (core : Core L N → Core L N → Nat)
    (center : N) (g : Nat) (state : Vertex L N g → A) (n : N) :
    incoming (edge core center g) state (.inl (.inr n)) =
      incoming core (fun u ↦ state (.inl u)) (.inr n) := by
  unfold incoming
  rw [Fintype.sum_sum_type]
  simp only [edge, retained_nonleader, Multiset.replicate_zero,
    Finset.sum_const_zero, add_zero]

/-- The source of a leader's singleton input is the final relay, or the
original center when no relay was added. -/
def leaderSource (center : N) (g : Nat) : Vertex L N g :=
  if hg : 0 < g then .inr ⟨g - 1, by omega⟩ else .inl (.inr center)

/-- If a core leader only heard the selected fanout center, the extended
leader hears exactly the final relay (or that center for an empty path). -/
theorem leader_incoming {A : Type} (core : Core L N → Core L N → Nat)
    (center : N) (g : Nat) (state : Vertex L N g → A) (l : L)
    (singleSource : ∀ u, core u (.inl l) = if u = .inr center then 1 else 0) :
    incoming (edge core center g) state (.inl (.inl l)) = {state (leaderSource center g)} := by
  classical
  unfold incoming
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type]
  simp only [edge, retained, singleSource, Sum.inl_ne_inr, if_false,
    Multiset.replicate_zero, Finset.sum_const_zero, zero_add, Sum.inr.injEq]
  by_cases hg : 0 < g
  · have hretained : ∀ n : N, (if n = center ∧ 0 < g then 0 else if n = center then 1 else 0) = 0 := by
      intro n
      by_cases hn : n = center <;> simp [hn, hg]
    simp only [hretained, Multiset.replicate_zero, Finset.sum_const_zero, zero_add]
    let last : Fin g := ⟨g - 1, by omega⟩
    have heq : ∀ i : Fin g, i.val + 1 = g ↔ i = last := fun i ↦ by
      simp only [Fin.ext_iff, last]
      omega
    simp only [heq]
    calc
      _ = ∑ i : Fin g, if i = last then ({state (.inr i)} : Multiset A) else 0 := by
        apply Finset.sum_congr rfl
        intro i _
        split_ifs <;> simp
      _ = _ := by simp [leaderSource, hg, last]
  · have hz : g = 0 := by omega
    subst g
    simp only [show ¬ 0 < 0 by omega, and_false, if_false]
    calc
      _ = ∑ n : N, if n = center then ({state (.inl (.inr n))} : Multiset A) else 0 := by
        simp only [Finset.univ_eq_empty, Finset.sum_empty, add_zero]
        apply Finset.sum_congr rfl
        intro n _
        split_ifs <;> simp
      _ = _ := by simp [leaderSource]

/-- A relay receives ell identical copies of its immediately preceding state. -/
def relaySource (center : N) (g : Nat) (i : Fin g) : Vertex L N g :=
  if hi : i.val = 0 then .inl (.inr center)
  else .inr ⟨i.val - 1, by omega⟩

theorem relay_incoming {A : Type} (core : Core L N → Core L N → Nat)
    (center : N) (g : Nat) (state : Vertex L N g → A) (i : Fin g) :
    incoming (edge core center g) state (.inr i) =
      Multiset.replicate (Fintype.card L) (state (relaySource center g i)) := by
  classical
  unfold incoming
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type]
  simp only [edge, Sum.inl_ne_inr, false_and, if_false,
    Multiset.replicate_zero, Finset.sum_const_zero, zero_add, Sum.inr.injEq]
  by_cases hi : i.val = 0
  · have hnone : ∀ j : Fin g, ¬ j.val + 1 = i.val := fun j ↦ by omega
    simp only [hnone, if_false, Multiset.replicate_zero, Finset.sum_const_zero, add_zero]
    simp only [hi, and_true]
    calc
      _ = ∑ n : N, if n = center then Multiset.replicate (Fintype.card L) (state (.inl (.inr n))) else 0 := by
        apply Finset.sum_congr rfl
        intro n _
        split_ifs <;> simp
      _ = _ := by simp [relaySource, hi]
  · have hpositive : 0 < i.val := by omega
    let previous : Fin g := ⟨i.val - 1, by omega⟩
    have heq : ∀ j : Fin g, j.val + 1 = i.val ↔ j = previous := fun j ↦ by
      simp only [Fin.ext_iff, previous]
      omega
    simp only [hi, and_false, if_false, Multiset.replicate_zero,
      Finset.sum_const_zero, zero_add, heq]
    calc
      _ = ∑ j : Fin g, if j = previous then Multiset.replicate (Fintype.card L) (state (.inr j)) else 0 := by
        apply Finset.sum_congr rfl
        intro j _
        split_ifs <;> simp
      _ = _ := by simp [relaySource, hi, previous]

omit [DecidableEq L] [DecidableEq N] in
@[simp] theorem leader_count (g : Nat) : Counting.leaderCount (leader (L := L) (N := N) (g := g)) = Fintype.card L := by
  classical
  unfold Counting.leaderCount
  rw [Finset.card_eq_sum_ones, Finset.sum_filter, Fintype.sum_sum_type, Fintype.sum_sum_type]
  simp [leader]

omit [Fintype N] in
/-- The selected original center reaches every relay along the inserted path. -/
theorem center_reaches_relay (core : Core L N → Core L N → Nat) (center : N)
    (g : Nat) (positive : 0 < Fintype.card L) (i : Fin g) :
    Relation.ReflTransGen (fun u v ↦ 0 < edge core center g u v)
      (.inl (.inr center)) (.inr i) := by
  cases g with
  | zero => exact Fin.elim0 i
  | succ g =>
      induction i using Fin.induction with
      | zero => exact .single (by simpa [edge] using positive)
      | succ i ih => exact ih.tail (by simpa [edge] using positive)

omit [Fintype N] in
/-- Each relay reaches every leader through the remaining inserted path. -/
theorem relay_reaches_leader (core : Core L N → Core L N → Nat) (center : N)
    (g : Nat) (positive : 0 < Fintype.card L) (i : Fin g) (l : L) :
    Relation.ReflTransGen (fun u v ↦ 0 < edge core center g u v)
      (.inr i) (.inl (.inl l)) := by
  cases g with
  | zero => exact Fin.elim0 i
  | succ g =>
      induction i using Fin.reverseInduction with
      | last => exact .single (by simp [edge])
      | cast i ih => exact ih.head (by simpa [edge] using positive)

omit [Fintype N] in
/-- Every positive original arc survives as a directed path. -/
theorem core_arc_path (core : Core L N → Core L N → Nat) (center : N)
    (g : Nat) (positive : 0 < Fintype.card L) (u v : Core L N)
    (arc : 0 < core u v) :
    Relation.ReflTransGen (fun u v ↦ 0 < edge core center g u v) (.inl u) (.inl v) := by
  cases u with
  | inl l =>
      cases v <;> exact .single arc
  | inr n =>
      cases v with
      | inr n' => exact .single arc
      | inl l =>
          by_cases hremoved : n = center ∧ 0 < g
          · obtain ⟨hn, hg⟩ := hremoved
            subst n
            let first : Fin g := ⟨0, hg⟩
            exact (center_reaches_relay core center g positive first).trans
              (relay_reaches_leader core center g positive first l)
          · exact .single (by simpa [edge, retained, hremoved] using arc)

omit [Fintype N] in
/-- Original reachability lifts through the replacement. -/
theorem core_path (core : Core L N → Core L N → Nat) (center : N)
    (g : Nat) (positive : 0 < Fintype.card L) (u v : Core L N)
    (path : Relation.ReflTransGen (fun u v ↦ 0 < core u v) u v) :
    Relation.ReflTransGen (fun u v ↦ 0 < edge core center g u v) (.inl u) (.inl v) := by
  induction path with
  | refl => exact .refl
  | tail path arc ih => exact ih.trans (core_arc_path core center g positive _ _ arc)

omit [Fintype N] in
/-- Replacing the selected fanout by relays preserves strong connectivity. -/
theorem stronglyConnected (core : Core L N → Core L N → Nat) (center : N)
    (g : Nat) (positive : 0 < Fintype.card L)
    (connected : StronglyConnected (fun u v ↦ 0 < core u v)) :
    StronglyConnected (fun u v ↦ 0 < edge core center g u v) := by
  obtain ⟨l⟩ := Fintype.card_pos_iff.mp positive
  intro u v
  have toCenter : Relation.ReflTransGen (fun u v ↦ 0 < edge core center g u v)
      u (.inl (.inr center)) := by
    cases u with
    | inl u => exact core_path core center g positive u (.inr center) (connected _ _)
    | inr i =>
        exact (relay_reaches_leader core center g positive i l).trans
          (core_path core center g positive (.inl l) (.inr center) (connected _ _))
  have fromCenter : Relation.ReflTransGen (fun u v ↦ 0 < edge core center g u v)
      (.inl (.inr center)) v := by
    cases v with
    | inl v => exact core_path core center g positive (.inr center) v (connected _ _)
    | inr i => exact center_reaches_relay core center g positive i
  exact toCenter.trans fromCenter

/-- A common core degree bound (at least ell) also bounds all relay degrees. -/
theorem outdegree_le (core : Core L N → Core L N → Nat) (center : N)
    (g D : Nat) (fanout : ∀ l, core (.inr center) (.inl l) = 1)
    (coreBound : ∀ u, (∑ v, core u v) ≤ D) (relayBound : Fintype.card L ≤ D)
    (u : Vertex L N g) : (∑ v, edge core center g u v) ≤ D := by
  cases u with
  | inl u => simpa only [core_outdegree core center g fanout] using coreBound u
  | inr i => simpa only [relay_outdegree core center g i] using relayBound

end Counting.LowerSeveralRelay
