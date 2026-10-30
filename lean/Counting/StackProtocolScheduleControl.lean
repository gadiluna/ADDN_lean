import Counting.StackProtocolScheduleCandidates

namespace Counting.StackMachine.ProtocolSchedule
open Routine EncodingPrograms
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

def selectedOutput (leaders round : Nat) : Option (Nat×Nat) :=
  if leaders=1 then
    if round%2=1 then some (round/2+1,round/2+1) else none
  else if round%2=1 then none
  else if round/2+1≤ leaders then none else some (round/2+1,round/2)

abbrev selectLeader : Routine 14 := sequence oneLeader (branchRoutine 2 singleRound manyRound)

theorem selectLeader_executes (leaders round : Nat) :
    ∃ time output,time≤ 150*(leaders.size+round.size+1) ∧
      Executes selectLeader (fields leaders round 0 0 []) time output ∧
      output 1=outputWord (selectedOutput leaders round) := by
  obtain ⟨a,abound,arun⟩:=oneLeader_executes leaders round
  by_cases single:leaders=1
  · simp only [single,decide_true] at arun
    obtain ⟨b,output,bbound,brun,result⟩:=singleRound_executes 1 round
    have branch:=branch_executes_true (2:Fin 16) singleRound manyRound
      (fields 1 round 0 0 [true]) output [] b
      (by simp [fields,file]) (by rw [fields_pop_flag];exact brun)
    refine ⟨a+1+(1+b),output,?_,?_,?_⟩
    · omega
    · simpa only [single] using arun.sequence branch
    · simpa [selectedOutput,single] using result
  · simp only [single,decide_false] at arun
    obtain ⟨b,output,bbound,brun,result⟩:=manyRound_executes leaders round
    have branch:=branch_executes_false (2:Fin 16) singleRound manyRound
      (fields leaders round 0 0 [false]) output [] b
      (by simp [fields,file]) (by rw [fields_pop_flag];exact brun)
    exact ⟨_,_,by omega,arun.sequence branch,by simpa [selectedOutput,single] using result⟩

abbrev checkRound : Routine 14 := sequence compareRound (branchRoutine 2 reject selectLeader)

theorem checkRound_executes (leaders round : Nat) :
    ∃ time output,time≤ 180*(leaders.size+round.size+1) ∧
      Executes checkRound (fields leaders round 0 0 []) time output ∧
      output 1=outputWord (if round≤ leaders then none else selectedOutput leaders round) := by
  obtain ⟨a,abound,arun⟩:=compareRound_executes leaders round 0 0
  by_cases early:round≤ leaders
  · simp only [early,decide_true] at arun
    obtain ⟨output,b,result⟩:=reject_executes leaders round 0 0
    have branch:=branch_executes_true (2:Fin 16) reject selectLeader
      (fields leaders round 0 0 [true]) output [] 1
      (by simp [fields,file]) (by rw [fields_pop_flag];exact b)
    exact ⟨_,_,by omega,arun.sequence branch,by simpa [early] using result⟩
  · simp only [early,decide_false] at arun
    obtain ⟨b,output,bbound,brun,result⟩:=selectLeader_executes leaders round
    have branch:=branch_executes_false (2:Fin 16) reject selectLeader
      (fields leaders round 0 0 [false]) output [] b
      (by simp [fields,file]) (by rw [fields_pop_flag];exact brun)
    exact ⟨_,_,by omega,arun.sequence branch,by simpa [early] using result⟩

abbrev body : Routine 14 := sequence zeroLeader (branchRoutine 2 reject checkRound)

/-- The actual finite control checks zero leaders, the early-round guard,
leader multiplicity, parity, and the final candidate threshold. -/
theorem body_executes (leaders round : Nat) :
    ∃ time output,time≤ 200*(leaders.size+round.size+1) ∧
      Executes body (fields leaders round 0 0 []) time output ∧
      output 1=outputWord (Executable.candidateAt leaders round) := by
  obtain ⟨a,abound,arun⟩:=zeroLeader_executes leaders round
  by_cases zero:leaders=0
  · simp only [zero,decide_true] at arun
    obtain ⟨output,b,result⟩:=reject_executes 0 round 0 0
    have branch:=branch_executes_true (2:Fin 16) reject checkRound
      (fields 0 round 0 0 [true]) output [] 1
      (by simp [fields,file]) (by rw [fields_pop_flag];exact b)
    refine ⟨a+1+(1+1),output,by omega,?_,?_⟩
    · simpa only [zero] using arun.sequence branch
    · simpa [Executable.candidateAt,zero] using result
  · simp only [zero,decide_false] at arun
    obtain ⟨b,output,bbound,brun,result⟩:=checkRound_executes leaders round
    have branch:=branch_executes_false (2:Fin 16) reject checkRound
      (fields leaders round 0 0 [false]) output [] b
      (by simp [fields,file]) (by rw [fields_pop_flag];exact brun)
    refine ⟨_,_,by omega,arun.sequence branch,?_⟩
    rw [←candidateFromParity_eq]
    simpa [candidateFromParity,zero,selectedOutput] using result

end Counting.StackMachine.ProtocolSchedule
