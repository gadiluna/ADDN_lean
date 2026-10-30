import Counting.StackProtocolScheduleCandidates
import Counting.StackRoutineIsolateHalt

namespace Counting.StackMachine.CoreSchedule
open Routine EncodingPrograms ProtocolSchedule
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 10000

def candidate (leaders round : Nat) : Option (Nat×Nat) :=
  if round%2=1 then
    if leaders≤ round/2+1 then some (round/2+1,round/2+1) else none
  else none

def minimumRoles : Fin 6 ↪ Fin 16 := ⟨![8,10,2,3,4,5],by decide⟩
abbrev compareMinimum : Routine 14 := Binary.preservingComparison 10 minimumRoles

theorem compareMinimum_executes (leaders round m last : Nat) :
    ∃ time≤ 7*(leaders.size+m.size)+9,
      Executes compareMinimum (fields leaders round m last []) time
        (fields leaders round m last [decide (leaders≤ m)]) := by
  have run:=Binary.preservingComparison_executes 10 minimumRoles (fields leaders round m last []) rfl rfl rfl
  change Executes _ _ (Binary.preservingCompareCost leaders.bits m.bits)
    (Function.update (fields leaders round m last []) 2 [Binary.compareBits true leaders.bits m.bits]) at run
  rw [compare_natural] at run
  have target:Function.update (fields leaders round m last []) 2 [decide (leaders≤ m)]=
      fields leaders round m last [decide (leaders≤ m)] := by
    funext r;by_cases flag:r=2 <;> simp [fields,file,flag]
  rw [target] at run
  exact ⟨_,by simpa only [Encoding.bits_length] using Binary.preservingCompareCost_le leaders.bits m.bits,run⟩

abbrev checkMinimum : Routine 14 := sequence compareMinimum (branchRoutine 2 emitCandidate reject)

theorem checkMinimum_executes (leaders round m last : Nat) :
    ∃ time output,time≤ 30*(leaders.size+m.size+last.size+1) ∧
      Executes checkMinimum (fields leaders round m last []) time output ∧
      output 1=outputWord (if leaders≤ m then some (m,last) else none) := by
  obtain ⟨a,abound,arun⟩:=compareMinimum_executes leaders round m last
  by_cases enough:leaders≤ m
  · simp only [enough,decide_true] at arun
    have b:=emitCandidate_executes leaders round m last
    have branch:=branch_executes_true (2:Fin 16) emitCandidate reject
      (fields leaders round m last [true]) _ [] _
      (by simp [fields,file]) (by rw [fields_pop_flag];exact b)
    exact ⟨_,_,by omega,arun.sequence branch,by simp [file,enough]⟩
  · simp only [enough,decide_false] at arun
    obtain ⟨output,b,result⟩:=reject_executes leaders round m last
    have branch:=branch_executes_false (2:Fin 16) emitCandidate reject
      (fields leaders round m last [false]) output [] 1
      (by simp [fields,file]) (by rw [fields_pop_flag];exact b)
    exact ⟨_,_,by omega,arun.sequence branch,by simpa [enough] using result⟩

abbrev choose : Routine 14 := sequence incrementCandidate (sequence saveLast checkMinimum)

theorem choose_executes (leaders round half : Nat) :
    ∃ time output,time≤ 150*(leaders.size+half.size+1) ∧
      Executes choose (fields leaders round half 0 []) time output ∧
      output 1=outputWord (if leaders≤ half+1 then some (half+1,half+1) else none) := by
  obtain ⟨a,abound,arun⟩:=incrementCandidate_executes leaders round half 0
  have brun:=saveLast_executes leaders round (half+1)
  obtain ⟨c,output,cbound,crun,result⟩:=checkMinimum_executes leaders round (half+1) (half+1)
  have size:=size_succ_bound half
  exact ⟨_,output,by omega,arun.sequence (brun.sequence crun),result⟩

abbrev body : Routine 14 := sequence readRound (branchRoutine 2 choose reject)

theorem body_executes (leaders round : Nat) :
    ∃ time output,time≤ 200*(leaders.size+round.size+1) ∧
      Executes body (fields leaders round 0 0 []) time output ∧
      output 1=outputWord (candidate leaders round) := by
  have a:=readRound_executes leaders round
  have halfBits:(round/2).size≤ round.size:=Nat.size_le_size (Nat.div_le_self round 2)
  by_cases odd:round%2=1
  · simp only [odd,decide_true] at a
    obtain ⟨b,output,bbound,brun,result⟩:=choose_executes leaders round (round/2)
    have branch:=branch_executes_true (2:Fin 16) choose reject
      (fields leaders round (round/2) 0 [true]) output [] b
      (by simp [fields,file]) (by rw [fields_pop_flag];exact brun)
    exact ⟨_,output,by omega,a.sequence branch,by simpa [candidate,odd] using result⟩
  · simp only [odd,decide_false] at a
    obtain ⟨output,b,result⟩:=reject_executes leaders round (round/2) 0
    have branch:=branch_executes_false (2:Fin 16) choose reject
      (fields leaders round (round/2) 0 [false]) output [] 1
      (by simp [fields,file]) (by rw [fields_pop_flag];exact b)
    exact ⟨_,output,by omega,a.sequence branch,by simpa [candidate,odd] using result⟩

abbrev completeRaw : Routine 14 := sequence parse body
abbrev complete : Routine 14 := isolate completeRaw

/-- The core schedule uses the actual round parity and binary threshold;
there is one candidate and its prefix length equals its candidate value. -/
theorem complete_executes (leaders round : Nat) :
    ∃ time≤ 4000*((inputWord leaders round).length+1),
      Executes complete (inputStore 14 (inputWord leaders round)) time
        (outputStore 14 (outputWord (candidate leaders round))) := by
  have a:=parse_executes leaders round
  obtain ⟨b,output,bbound,brun,result⟩:=body_executes leaders round
  have rawRun:=a.sequence brun
  obtain ⟨finish,ran,halted,stored⟩:=rawRun
  have rawHalt : ∃ time last,time≤ 210*(leaders.size+round.size+1) ∧
      HaltsAt completeRaw.program (inputWord leaders round) time last ∧
      last.store 1=outputWord (candidate leaders round) :=
    ⟨_,finish,by omega,⟨ran,halted⟩,by rw [stored];exact result⟩
  obtain ⟨time,bounded,run⟩:=isolate_halts completeRaw (inputWord leaders round)
    (outputWord (candidate leaders round)) _ rawHalt
  refine ⟨time,bounded.trans ?_,run⟩
  simp only [inputWord,List.length_append,Encoding.natural_length]
  omega

end Counting.StackMachine.CoreSchedule
