import Counting.StackEncodingBranch
import Counting.EncodingBinary

namespace Counting.StackMachine.EncodingPrograms

def countNext (header : List Bool) (current : Nat) : Nat :=
  if current.bits=header then current else current+1

def countRun (header : List Bool) (current : Nat) : Nat → Nat
  | 0 => current
  | fuel+1 => countRun header (countNext header current) fuel

theorem countNext_le (header : List Bool) (current : Nat) : countNext header current ≤ current+1 := by
  unfold countNext
  split_ifs <;> omega

theorem countRun_le (header : List Bool) (current fuel : Nat) : countRun header current fuel ≤ current+fuel := by
  induction fuel generalizing current with
  | zero => rfl
  | succ fuel ih =>
    have bounded := ih (countNext header current)
    have next := countNext_le header current
    simp only [countRun]
    omega

theorem countRun_fixed (value fuel : Nat) : countRun value.bits value fuel = value := by
  induction fuel with
  | zero => rfl
  | succ fuel ih => simpa only [countRun,countNext,ite_true] using ih

theorem countRun_natural (value current fuel : Nat) (before : current≤value) :
    countRun value.bits current fuel = min (current+fuel) value := by
  induction fuel generalizing current with
  | zero => simp [countRun,Nat.min_eq_left before]
  | succ fuel ih =>
    by_cases same : current=value
    · subst current
      rw [countRun_fixed]
      omega
    · have different : current.bits≠value.bits := fun eq => same (Encoding.bits_injective eq)
      simp only [countRun,countNext,if_neg different]
      rw [ih (current+1) (by omega)]
      congr 1
      omega

/-- A binary header is never expanded beyond the supplied unary budget.
Even noncanonical or enormous headers are rejected after at most `budget`
iterations of the bounded outer loop. -/
theorem countRun_accept_iff (header : List Bool) (budget : Nat) :
    (countRun header 0 budget).bits=header ↔ ∃ value≤budget, header=value.bits := by
  constructor
  · intro accepted
    exact ⟨countRun header 0 budget,by simpa using countRun_le header 0 budget,accepted.symm⟩
  · rintro ⟨value,bounded,rfl⟩
    rw [countRun_natural value 0 budget (Nat.zero_le _)]
    simp only [Nat.zero_add,Nat.min_eq_right bounded]

end Counting.StackMachine.EncodingPrograms
