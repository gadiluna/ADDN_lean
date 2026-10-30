import Counting.FullTransitionRealizability

/-! Boundary checks for the full-transition interface. These are kernel-checked
existence statements, including cases where the node graph has only one node. -/

namespace Counting.FullTransition.Examples

def singleClass (k : Nat) : Data Bool Unit where
  parent _ := false
  degree _ := k
  red u _ := if u = false then k else 0

/-- A singleton can have any number of loops, including zero. The unused
old class `true` requires no artificial positive degree or connectivity. -/
theorem singleton_loops (k : Nat) :
    ∃ E : Agents (fun _ : Unit => 1) → Agents (fun _ : Unit => 1) → Nat,
      (singleClass k).Realizes Sigma.fst E := by
  apply Data.realizing_transition_singleton
  · intro u
    cases u <;> simp [singleClass]
  · simp

/-- Arbitrarily many agents in the same class can form a directed cycle.
The proof must connect distinct agents even though the class graph has one
vertex, so its reflexive paths alone would not suffice. -/
theorem many_agents_one_class (n : Nat) (many : 1 < n) :
    ∃ E : Agents (fun _ : Unit => n) → Agents (fun _ : Unit => n) → Nat,
      (singleClass 1).Realizes Sigma.fst E := by
  apply (Data.realizing_transition (singleClass 1) (fun _ : Unit => n)
    (by intro _; omega) (by intro u; cases u <;> simp [singleClass])
    (by simpa using many)).mpr
  refine ⟨?_, ?_, ?_⟩
  · intro v
    simp [singleClass]
  · intro v
    simp [singleClass]
  · intro v w
    have eq : v = w := Subsingleton.elim _ _
    subst w
    exact .refl

/-- With several agents, balanced zero degrees do not suffice. -/
theorem many_agents_zero_degree_impossible (n : Nat) (many : 1 < n) :
    ¬ ∃ E : Agents (fun _ : Unit => n) → Agents (fun _ : Unit => n) → Nat,
      (singleClass 0).Realizes Sigma.fst E := by
  intro h
  have conditions := (Data.realizing_transition (singleClass 0) (fun _ : Unit => n)
    (by intro _; omega) (by intro u; cases u <;> simp [singleClass])
    (by simpa using many)).mp h
  exact Nat.lt_irrefl 0 (conditions.1 ())

end Counting.FullTransition.Examples
