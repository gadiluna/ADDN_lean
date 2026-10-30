import Counting.LowerSeveralCycles

/-!
# The one fixed final cycle

The cyclic order places the designated observer after all original
nonleaders and all relays, followed by the remaining leaders. This is
exactly the final cycle of the appendix, repeated without modification.
-/

namespace Counting.LowerSeveralFinal
open DirectedCounting LowerSeveralPhases
open scoped BigOperators

abbrev Vertices (k q g : Nat) := LowerSeveralRelay.Vertex (Leaders k) (Fin (q + 1)) g

def rank (k q g : Nat) : Vertices k q g → Fin (k + 2 + (q + 1) + g)
  | .inl (.inl l) => if l.val < k + 1 then ⟨l.val, by omega⟩
      else ⟨k + 1 + (q + 1) + g, by omega⟩
  | .inl (.inr n) => ⟨k + 1 + n.val, by omega⟩
  | .inr j => ⟨k + 1 + (q + 1) + j.val, by omega⟩

def unrank (k q g : Nat) (i : Fin (k + 2 + (q + 1) + g)) : Vertices k q g :=
  if hL : i.val < k + 1 then .inl (.inl ⟨i.val, by omega⟩)
  else if hN : i.val < k + 1 + (q + 1) then .inl (.inr ⟨i.val - (k + 1), by omega⟩)
  else if hR : i.val < k + 1 + (q + 1) + g then .inr ⟨i.val - (k + 1 + (q + 1)), by omega⟩
  else .inl (.inl (observer k))

theorem unrank_rank (k q g : Nat) (v : Vertices k q g) : unrank k q g (rank k q g v) = v := by
  cases v with
  | inl v =>
      cases v with
      | inl l =>
          by_cases hl : l.val < k + 1
          · simp [rank, hl, unrank]
          · have hval : l.val = k + 1 := by omega
            simp only [rank, if_neg hl, unrank, Fin.val_mk]
            rw [dif_neg (by omega), dif_neg (by omega), dif_neg (by omega)]
            congr 2
            apply Fin.ext
            simpa [observer] using hval.symm
      | inr n =>
          have hnot : ¬ k + 1 + n.val < k + 1 := by omega
          have hbound : k + 1 + n.val < k + 1 + (q + 1) := by omega
          simp [rank, unrank, hnot, hbound]
  | inr j =>
      have hnotL : ¬ k + 1 + (q + 1) + j.val < k + 1 := by omega
      have hnotN : ¬ k + 1 + (q + 1) + j.val < k + 1 + (q + 1) := by omega
      have hbound : k + 1 + (q + 1) + j.val < k + 1 + (q + 1) + g := by omega
      simp [rank, unrank, hnotL, hnotN, hbound]

theorem rank_unrank (k q g : Nat) (i : Fin (k + 2 + (q + 1) + g)) :
    rank k q g (unrank k q g i) = i := by
  unfold unrank
  split_ifs <;> apply Fin.ext <;> simp_all [rank, observer] <;> omega

def rankEquiv (k q g : Nat) : Vertices k q g ≃ Fin (k + 2 + (q + 1) + g) where
  toFun := rank k q g
  invFun := unrank k q g
  left_inv := unrank_rank k q g
  right_inv := rank_unrank k q g

def graph (k q g : Nat) := relabel (rankEquiv k q g) (LowerSeveralCycles.edge (k + 2 + (q + 1) + g))

theorem graph_valid (k q g : Nat) : RoundValid (graph k q g) (k + 2) := by
  apply relabel_valid
  constructor
  · exact LowerSeveralCycles.connected _
  · exact LowerSeveralCycles.loopless _ (by omega)
  · intro u v
    exact (LowerSeveralCycles.multiplicity _ u v).trans (by omega)
  · intro u
    rw [LowerSeveralCycles.degree]
    simpa using Nat.pow_le_pow_left (show 1 ≤ k + 2 by omega) 2

theorem graph_degree (k q g : Nat) (v : Vertices k q g) : (∑w, graph k q g v w) = 1 := by
  unfold graph
  rw [relabel_degree, LowerSeveralCycles.degree]

/-- Consecutive non-wrapping positions identify an exact singleton input. -/
theorem graph_incoming_of_consecutive {A : Type} (k q g : Nat) (state : Vertices k q g → A)
    (source target : Vertices k q g)
    (adjacent : (rank k q g source).val + 1 = (rank k q g target).val) :
    incoming (graph k q g) state target = {state source} := by
  unfold graph
  rw [relabel_incoming, LowerSeveralCycles.incoming_eq]
  have h := LowerSeveralCycles.rotate_of_next _ (rank k q g source) (rank k q g target) adjacent
  have hpred : (finRotate _).symm (rank k q g target) = rank k q g source :=
    (Equiv.symm_apply_eq _).mpr h.symm
  change {state ((rankEquiv k q g).symm ((finRotate _).symm (rank k q g target)))} = _
  rw [hpred]
  exact congrArg (fun v ↦ ({state v} : Multiset A)) (unrank_rank k q g source)

def unitFin : Unit ≃ Fin 1 where
  toFun := fun _ ↦ 0
  invFun := fun _ ↦ ()
  left_inv := fun u ↦ by cases u; rfl
  right_inv := fun i ↦ Subsingleton.elim _ _

def smallEquiv (k g : Nat) : Small k g ≃ Vertices k 0 g :=
  Equiv.sumCongr (Equiv.sumCongr (Equiv.refl _) unitFin) (Equiv.refl _)

def smallGraph (k g : Nat) := relabel (smallEquiv k g) (graph k 0 g)
def largeGraph (k g : Nat) := graph k (k + 1) g

theorem smallGraph_valid (k g : Nat) : RoundValid (smallGraph k g) (k + 2) :=
  relabel_valid (smallEquiv k g) _ _ (graph_valid k 0 g)

theorem largeGraph_valid (k g : Nat) : RoundValid (largeGraph k g) (k + 2) := graph_valid k (k + 1) g

theorem smallGraph_degree (k g : Nat) (v : Small k g) : (∑w, smallGraph k g v w) = 1 := by
  unfold smallGraph
  rw [relabel_degree, graph_degree]

theorem largeGraph_degree (k g : Nat) (v : Large k g) : (∑w, largeGraph k g v w) = 1 := graph_degree k (k + 1) g v

/-- The shared consecutive suffix is y,z1,...,zg,x, indexed from zero. -/
def tailVertex (k q g : Nat) (j : Fin (g + 2)) : Vertices k q g :=
  if hzero : j.val = 0 then .inl (.inr (Fin.last q))
  else if hj : j.val ≤ g then .inr ⟨j.val - 1, by omega⟩
  else .inl (.inl (observer k))

theorem rank_tailVertex (k q g : Nat) (j : Fin (g + 2)) :
    (rank k q g (tailVertex k q g j)).val = k + 1 + q + j.val := by
  unfold tailVertex
  split_ifs with hzero hrelay
  · simp only [rank, Fin.val_last, Fin.val_mk, hzero, Nat.add_zero]
  · simp only [rank, Fin.val_mk]
    omega
  · simp only [rank, observer, Fin.val_last, lt_self_iff_false, if_false, Fin.val_mk]
    omega

@[simp] theorem tailVertex_zero (k q g : Nat) : tailVertex k q g 0 = .inl (.inr (Fin.last q)) := by
  simp [tailVertex]

@[simp] theorem tailVertex_last (k q g : Nat) : tailVertex k q g (Fin.last (g + 1)) = .inl (.inl (observer k)) := by
  simp [tailVertex]

def previousTail (g : Nat) (j : Fin (g + 2)) : Fin (g + 2) := ⟨j.val - 1, by omega⟩

/-- Every positive suffix position hears just its preceding suffix position. -/
theorem tail_incoming {A : Type} (k q g : Nat) (state : Vertices k q g → A)
    (j : Fin (g + 2)) (positive : 0 < j.val) :
    incoming (graph k q g) state (tailVertex k q g j) =
      {state (tailVertex k q g (previousTail g j))} := by
  apply graph_incoming_of_consecutive
  rw [rank_tailVertex, rank_tailVertex]
  dsimp [previousTail]
  omega

def smallTail (k g : Nat) (j : Fin (g + 2)) : Small k g := (smallEquiv k g).symm (tailVertex k 0 g j)
def largeTail (k g : Nat) (j : Fin (g + 2)) : Large k g := tailVertex k (k + 1) g j

@[simp] theorem smallTail_zero (k g : Nat) : smallTail k g 0 = smallNonleader k g := by
  simp [smallTail, smallEquiv, unitFin, smallNonleader]

@[simp] theorem largeTail_zero (k g : Nat) : largeTail k g 0 = largeNonleader k g (observer k) := by
  simp [largeTail, largeNonleader, observer]

@[simp] theorem smallTail_last (k g : Nat) : smallTail k g (Fin.last (g + 1)) = smallLeader k g (observer k) := by
  simp [smallTail, smallEquiv, smallLeader]

@[simp] theorem largeTail_last (k g : Nat) : largeTail k g (Fin.last (g + 1)) = largeLeader k g (observer k) := by
  simp [largeTail, largeLeader]

theorem smallTail_step {A : Type} (k g : Nat) (state : Small k g → A)
    (j : Fin (g + 2)) (positive : 0 < j.val) :
    step (smallGraph k g) state (smallTail k g j) =
      (state (smallTail k g j), 1, {state (smallTail k g (previousTail g j))}) := by
  dsimp only [step]
  refine Prod.ext rfl ?_
  apply Prod.ext (smallGraph_degree k g _)
  unfold smallGraph smallTail
  rw [relabel_incoming]
  simp only [Equiv.apply_symm_apply]
  exact tail_incoming k 0 g _ j positive

theorem largeTail_step {A : Type} (k g : Nat) (state : Large k g → A)
    (j : Fin (g + 2)) (positive : 0 < j.val) :
    step (largeGraph k g) state (largeTail k g j) =
      (state (largeTail k g j), 1, {state (largeTail k g (previousTail g j))}) := by
  dsimp only [step]
  refine Prod.ext rfl ?_
  apply Prod.ext (largeGraph_degree k g _)
  exact tail_incoming k (k + 1) g state j positive

/-- The middle-phase endpoint provides every matched state in the common
suffix, including the no-relay case g=0. -/
theorem tail_matches_of_middle {A : Type} (k g : Nat) (a : Small k g → A) (b : Large k g → A)
    (observers : a (smallLeader k g (observer k)) = b (largeLeader k g (observer k)))
    (nonleaders : a (smallNonleader k g) = b (largeNonleader k g (observer k)))
    (relays : ∀ j, a (.inr j) = b (.inr j)) :
    ∀ j, a (smallTail k g j) = b (largeTail k g j) := by
  intro j
  by_cases hj0 : j.val = 0
  · have hj : j = 0 := Fin.ext hj0
    simpa only [hj, smallTail_zero, largeTail_zero] using nonleaders
  · by_cases hjg : j.val ≤ g
    · simpa [smallTail, largeTail, tailVertex, hj0, hjg, smallEquiv] using
        relays (⟨j.val - 1, by omega⟩ : Fin g)
    · have hj : j = Fin.last (g + 1) := Fin.ext (by simp; omega)
      simpa only [hj, smallTail_last, largeTail_last] using observers

/-- Differences advance by at most one suffix position per final cycle round. -/
theorem tail_step_preserves {A : Type} (k g t : Nat) (a : Small k g → A) (b : Large k g → A)
    (matched : ∀ j : Fin (g + 2), t ≤ j.val → a (smallTail k g j) = b (largeTail k g j)) :
    ∀ j : Fin (g + 2), t + 1 ≤ j.val →
      step (smallGraph k g) a (smallTail k g j) = step (largeGraph k g) b (largeTail k g j) := by
  intro j hj
  have hpos : 0 < j.val := by omega
  rw [smallTail_step k g a j hpos, largeTail_step k g b j hpos,
    matched j (by omega), matched (previousTail g j) (by dsimp [previousTail]; omega)]

/-- Repeating the fixed final graphs preserves observer histories for g+1
rounds after the common suffix is established. -/
theorem final_histories (k g offset : Nat)
    (G : Nat → Small k g → Small k g → Nat) (H : Nat → Large k g → Large k g → Nat)
    (labels : Small k g → Bool) (labels' : Large k g → Bool)
    (initial : ∀ j, history G labels offset (smallTail k g j) = history H labels' offset (largeTail k g j))
    (smallRounds : ∀ t, t < g + 1 → G (offset + t + 1) = smallGraph k g)
    (largeRounds : ∀ t, t < g + 1 → H (offset + t + 1) = largeGraph k g) :
    ∀ t, t ≤ g + 1 → history G labels (offset + t) (smallLeader k g (observer k)) =
      history H labels' (offset + t) (largeLeader k g (observer k)) := by
  have matched : ∀ t, t ≤ g + 1 → ∀ j : Fin (g + 2), t ≤ j.val →
      history G labels (offset + t) (smallTail k g j) =
        history H labels' (offset + t) (largeTail k g j) := by
    intro t
    induction t with
    | zero => intro _ j _; simpa using initial j
    | succ t ih =>
        intro ht j hj
        have hprev := ih (by omega)
        have hstep := tail_step_preserves k g t _ _ hprev j hj
        simp only [Nat.add_succ]
        change step (G (offset + t + 1)) (history G labels (offset + t)) (smallTail k g j) =
          step (H (offset + t + 1)) (history H labels' (offset + t)) (largeTail k g j)
        rw [smallRounds t (by omega), largeRounds t (by omega)]
        exact hstep
  intro t ht
  simpa only [smallTail_last, largeTail_last] using matched t ht (Fin.last (g + 1)) ht

end Counting.LowerSeveralFinal
