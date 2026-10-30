import Counting.Executable
import Counting.StackProtocolScheduleArithmetic

namespace Counting.StackMachine.ProtocolSchedule

def candidateFromParity (leaders round : Nat) : Option (Nat×Nat) :=
  if leaders=0 ∨ round≤ leaders then none
  else if leaders=1 then
    if round%2=1 then some (round/2+1,round/2+1) else none
  else if round%2=1 then none
  else if round/2+1≤ leaders then none else some (round/2+1,round/2)

/-- The finite control can branch on the least significant round bit,
without evaluating unary arithmetic or changing any schedule boundary. -/
theorem candidateFromParity_eq (leaders round : Nat) :
    candidateFromParity leaders round=Executable.candidateAt leaders round := by
  have remainder:=Nat.mod_lt round (by decide:0<2)
  by_cases early:leaders=0 ∨ round≤ leaders
  · simp [candidateFromParity,Executable.candidateAt,early]
  · by_cases single:leaders=1
    · by_cases odd:round%2=1
      · have half:(round+1)/2=round/2+1 := by omega
        simp [candidateFromParity,Executable.candidateAt,single,odd,half]
      · simp [candidateFromParity,Executable.candidateAt,single,odd]
    · by_cases odd:round%2=1
      · simp [candidateFromParity,Executable.candidateAt,early,single,odd]
      · have even:round%2=0 := by omega
        by_cases small:round/2+1≤ leaders
        · simp [candidateFromParity,Executable.candidateAt,early,single,even,small,Nat.not_lt.mpr small]
        · have large:leaders<round/2+1 := by omega
          simp [candidateFromParity,Executable.candidateAt,early,single,even,small,large]

end Counting.StackMachine.ProtocolSchedule
