import Counting.StackProtocolScheduleActions

namespace Counting.StackMachine.ProtocolSchedule
open Routine EncodingPrograms
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

theorem size_succ_bound (n : Nat) : (n+1).size≤ n.size+1 := by
  apply Nat.size_le.mpr
  have less:=Nat.lt_size_self n
  have positive:0<2^n.size:=by positivity
  rw [pow_succ]
  omega

theorem fields_pop_flag (leaders round candidate last : Nat) (bit : Bool) :
    Function.update (fields leaders round candidate last [bit]) 2 []=fields leaders round candidate last [] := by
  funext r;by_cases flag:r=2 <;> simp [fields,file,flag]

abbrev reject : Routine 14 := pushBit 1 false

theorem reject_executes (leaders round candidate last : Nat) :
    ∃ output,Executes reject (fields leaders round candidate last []) 1 output ∧ output 1=outputWord none := by
  have run:=pushBit_executes (1:Fin 16) false (fields leaders round candidate last [])
  exact ⟨_,run,by simp [fields,file,outputWord,Encoding.optional]⟩

abbrev singleCandidate : Routine 14 := sequence incrementCandidate (sequence saveLast emitCandidate)

theorem singleCandidate_executes (leaders round half : Nat) :
    ∃ time output,time≤ 50*(half.size+1) ∧
      Executes singleCandidate (fields leaders round half 0 []) time output ∧
      output 1=outputWord (some (half+1,half+1)) := by
  obtain ⟨a,abound,arun⟩:=incrementCandidate_executes leaders round half 0
  have b:=saveLast_executes leaders round (half+1)
  have c:=emitCandidate_executes leaders round (half+1) (half+1)
  have size:=size_succ_bound half
  exact ⟨_,_,by omega,arun.sequence (b.sequence c),by simp [file]⟩

abbrev checkCandidate : Routine 14 := sequence compareCandidate (branchRoutine 2 reject emitCandidate)

theorem checkCandidate_executes (leaders round candidate last : Nat) :
    ∃ time output,time≤ 30*(leaders.size+candidate.size+last.size+1) ∧
      Executes checkCandidate (fields leaders round candidate last []) time output ∧
      output 1=outputWord (if candidate≤ leaders then none else some (candidate,last)) := by
  obtain ⟨a,abound,arun⟩:=compareCandidate_executes leaders round candidate last
  by_cases small:candidate≤ leaders
  · simp only [small,decide_true] at arun
    obtain ⟨output,b,result⟩:=reject_executes leaders round candidate last
    have branch:=branch_executes_true (2:Fin 16) reject emitCandidate
      (fields leaders round candidate last [true]) output [] 1
      (by simp [fields,file]) (by rw [fields_pop_flag];exact b)
    exact ⟨_,_,by omega,arun.sequence branch,by simpa [small] using result⟩
  · simp only [small,decide_false] at arun
    have b:=emitCandidate_executes leaders round candidate last
    have branch:=branch_executes_false (2:Fin 16) reject emitCandidate
      (fields leaders round candidate last [false]) _ [] _
      (by simp [fields,file]) (by rw [fields_pop_flag];exact b)
    exact ⟨_,_,by omega,arun.sequence branch,by simp [file,small]⟩

abbrev manyCandidate : Routine 14 := sequence saveLast (sequence incrementCandidate checkCandidate)

theorem manyCandidate_executes (leaders round half : Nat) :
    ∃ time output,time≤ 100*(leaders.size+half.size+1) ∧
      Executes manyCandidate (fields leaders round half 0 []) time output ∧
      output 1=outputWord (if half+1≤ leaders then none else some (half+1,half)) := by
  have a:=saveLast_executes leaders round half
  obtain ⟨b,bbound,brun⟩:=incrementCandidate_executes leaders round half half
  obtain ⟨c,output,cbound,crun,result⟩:=checkCandidate_executes leaders round (half+1) half
  have size:=size_succ_bound half
  exact ⟨_,_,by omega,a.sequence (brun.sequence crun),result⟩

abbrev singleRound : Routine 14 := sequence readRound (branchRoutine 2 singleCandidate reject)

theorem singleRound_executes (leaders round : Nat) :
    ∃ time output,time≤ 60*(round.size+1) ∧
      Executes singleRound (fields leaders round 0 0 []) time output ∧
      output 1=outputWord (if round%2=1 then some (round/2+1,round/2+1) else none) := by
  have a:=readRound_executes leaders round
  have halfBits:(round/2).size≤ round.size:=Nat.size_le_size (Nat.div_le_self round 2)
  by_cases odd:round%2=1
  · simp only [odd,decide_true] at a
    obtain ⟨b,output,bbound,brun,result⟩:=singleCandidate_executes leaders round (round/2)
    have branch:=branch_executes_true (2:Fin 16) singleCandidate reject
      (fields leaders round (round/2) 0 [true]) output [] b
      (by simp [fields,file]) (by rw [fields_pop_flag];exact brun)
    exact ⟨_,_,by omega,a.sequence branch,by simpa [odd] using result⟩
  · simp only [odd,decide_false] at a
    obtain ⟨output,b,result⟩:=reject_executes leaders round (round/2) 0
    have branch:=branch_executes_false (2:Fin 16) singleCandidate reject
      (fields leaders round (round/2) 0 [false]) output [] 1
      (by simp [fields,file]) (by rw [fields_pop_flag];exact b)
    exact ⟨_,_,by omega,a.sequence branch,by simpa [odd] using result⟩

abbrev manyRound : Routine 14 := sequence readRound (branchRoutine 2 reject manyCandidate)

theorem manyRound_executes (leaders round : Nat) :
    ∃ time output,time≤ 120*(leaders.size+round.size+1) ∧
      Executes manyRound (fields leaders round 0 0 []) time output ∧
      output 1=outputWord (if round%2=1 then none else
        if round/2+1≤ leaders then none else some (round/2+1,round/2)) := by
  have a:=readRound_executes leaders round
  have halfBits:(round/2).size≤ round.size:=Nat.size_le_size (Nat.div_le_self round 2)
  by_cases odd:round%2=1
  · simp only [odd,decide_true] at a
    obtain ⟨output,b,result⟩:=reject_executes leaders round (round/2) 0
    have branch:=branch_executes_true (2:Fin 16) reject manyCandidate
      (fields leaders round (round/2) 0 [true]) output [] 1
      (by simp [fields,file]) (by rw [fields_pop_flag];exact b)
    exact ⟨_,_,by omega,a.sequence branch,by simpa [odd] using result⟩
  · simp only [odd,decide_false] at a
    obtain ⟨b,output,bbound,brun,result⟩:=manyCandidate_executes leaders round (round/2)
    have branch:=branch_executes_false (2:Fin 16) reject manyCandidate
      (fields leaders round (round/2) 0 [false]) output [] b
      (by simp [fields,file]) (by rw [fields_pop_flag];exact brun)
    exact ⟨_,_,by omega,a.sequence branch,by simpa [odd] using result⟩

end Counting.StackMachine.ProtocolSchedule
