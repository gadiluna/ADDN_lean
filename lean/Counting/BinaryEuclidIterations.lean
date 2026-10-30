import Mathlib.Data.Nat.Size
import Mathlib.Data.Nat.GCD.Basic
import Lean.Elab.Tactic.Omega

/-! A bit-length bound for the actual number of Euclidean updates.
The zero-divisor state is absorbing, matching a bounded executable loop. -/
namespace Counting.StackMachine.Binary

def euclidIter : Nat → Nat → Nat → Nat × Nat
  | 0, a, b => (a,b)
  | fuel+1, a, b => if b=0 then (a,0) else euclidIter fuel b (a%b)

@[simp] theorem euclidIter_zero_right (fuel a : Nat) : euclidIter fuel a 0 = (a,0) := by
  cases fuel <;> simp [euclidIter]

theorem euclidIter_succ (fuel a b : Nat) : euclidIter (fuel+1) a b =
    if b=0 then euclidIter fuel a b else euclidIter fuel b (a%b) := by
  by_cases zero : b=0 <;> simp [euclidIter,zero]

theorem gcd_euclid_step (a b : Nat) : Nat.gcd b (a%b) = Nat.gcd a b := by
  rw [Nat.gcd_comm b (a%b),←Nat.gcd_rec b a,Nat.gcd_comm b a]

/-- In two nonterminal steps the second operand loses at least one binary digit.
The explicit power form also covers operands at an exact power-of-two boundary. -/
theorem euclid_two_remainders_lt (a b k : Nat) (bound : b < 2^(k+1))
    (remainder : a%b ≠ 0) : b%(a%b) < 2^k := by
  by_cases zero : b=0
  · subst b
    simpa only [Nat.zero_mod] using (Nat.pow_pos (by decide : 0 < 2) : 0 < 2^k)
  have positive : 0 < a%b := Nat.pos_of_ne_zero remainder
  by_cases small : a%b < 2^k
  · exact lt_trans (Nat.mod_lt _ positive) small
  · have bp : 0 < b := Nat.pos_of_ne_zero zero
    have smaller := Nat.mod_lt a bp
    have twice : b < 2*(a%b) := by
      rw [pow_succ] at bound
      omega
    rw [Nat.mod_eq_sub_mod (by omega : a%b ≤ b)]
    rw [Nat.mod_eq_of_lt (by omega : b-a%b < a%b)]
    rw [pow_succ] at bound
    omega

theorem euclidIter_power_bound (k a b : Nat) (bound : b < 2^k) :
    euclidIter (2*k+1) a b = (Nat.gcd a b,0) := by
  induction k generalizing a b with
  | zero =>
      have zero : b=0 := by simpa using bound
      simp [zero]
  | succ k ih =>
      by_cases zero : b=0
      · simp [zero]
      · have fuel : 2*(k+1)+1 = (2*k+1)+1+1 := by omega
        rw [fuel,euclidIter,if_neg zero]
        by_cases remzero : a%b=0
        · simp [remzero,←gcd_euclid_step a b]
        · rw [euclidIter,if_neg remzero,
            ih (a%b) (b%(a%b)) (euclid_two_remainders_lt a b k bound remzero)]
          rw [gcd_euclid_step,gcd_euclid_step]

/-- A budget determined solely by the binary length of the second operand
suffices; it is independent of that operand's numeric value. -/
theorem euclidIter_size_bound (a b : Nat) :
    euclidIter (2*Nat.size b+1) a b = (Nat.gcd a b,0) :=
  euclidIter_power_bound (Nat.size b) a b (Nat.lt_size_self b)

/-- Every operand encountered by the bounded loop remains below the larger
initial operand. This invariant supports uniform costs for all loop bodies. -/
theorem euclidIter_le_max (fuel a b : Nat) :
    (euclidIter fuel a b).1 ≤ max a b ∧ (euclidIter fuel a b).2 ≤ max a b := by
  induction fuel generalizing a b with
  | zero => exact ⟨Nat.le_max_left a b,Nat.le_max_right a b⟩
  | succ fuel ih =>
      by_cases zero : b=0
      · simp [zero]
      · rw [euclidIter,if_neg zero]
        have next := ih b (a%b)
        have bound : max b (a%b) ≤ max a b := by
          exact max_le (Nat.le_max_right a b)
            (le_trans (Nat.le_of_lt (Nat.mod_lt a (Nat.pos_of_ne_zero zero)))
              (Nat.le_max_right a b))
        exact ⟨le_trans next.1 bound,le_trans next.2 bound⟩

theorem euclidIter_size_le (fuel a b : Nat) :
    Nat.size (euclidIter fuel a b).1 ≤ max (Nat.size a) (Nat.size b) ∧
      Nat.size (euclidIter fuel a b).2 ≤ max (Nat.size a) (Nat.size b) := by
  have bound := euclidIter_le_max fuel a b
  have first := Nat.size_le_size bound.1
  have second := Nat.size_le_size bound.2
  rcases le_total a b with order | order
  · rw [max_eq_right order] at first second
    exact ⟨le_trans first (Nat.le_max_right _ _),le_trans second (Nat.le_max_right _ _)⟩
  · rw [max_eq_left order] at first second
    exact ⟨le_trans first (Nat.le_max_left _ _),le_trans second (Nat.le_max_left _ _)⟩

end Counting.StackMachine.Binary
