import Counting.ComplexityComposition

namespace Counting.Machine

/-- One actual transition reads a Boolean output. Non-one symbols reject. -/
def booleanDecision : Program where
  states := 2
  code state symbol := if state.val=0 then
    some (if symbol=.one then 1 else 2,.write symbol) else none
  accept state := state==1

def booleanDecisionOutput (input : List Bool) : Config booleanDecision :=
  ⟨if input.headD false then 1 else 2,(initial booleanDecision input).tape⟩

theorem booleanDecision_halts (input : List Bool) : HaltsAt booleanDecision input 1 (booleanDecisionOutput input) := by
  cases input with
  | nil => exact ⟨rfl,rfl⟩
  | cons bit rest => cases bit <;> exact ⟨rfl,rfl⟩

theorem booleanDecision_accept (input : List Bool) :
    booleanDecision.accept (booleanDecisionOutput input).control=input.headD false := by
  cases input with
  | nil => rfl
  | cons bit rest => cases bit <;> rfl

theorem booleanDecision_decides : Complexity.DecidesIn booleanDecision {input | input.headD false=true}
    (Complexity.polynomial 1 0) := by
  constructor
  · intro input
    exact ⟨1,booleanDecisionOutput input,by simp [Complexity.polynomial],booleanDecision_halts input⟩
  · intro input
    rw [accepts_iff_of_halts (booleanDecision_halts input),booleanDecision_accept]
    rfl

end Counting.Machine

namespace Counting.Complexity

theorem ComputesCleanIn.boolean_decides {program : Machine.Program} {predicate : Word→Bool} {c k : Nat}
    (computes : ComputesCleanIn program (fun input => [predicate input]) (polynomial c k)) :
    DecidesIn (Machine.compose program Machine.booleanDecision) {input | predicate input=true}
      (polynomial (compositionCoefficient c 1 0) (compositionExponent k 0)) :=
  computes.decides Machine.booleanDecision_decides

end Counting.Complexity
