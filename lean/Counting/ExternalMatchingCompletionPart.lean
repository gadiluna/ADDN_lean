import Counting.ExternalMatchingGeneratorLayout

namespace Counting.External.MatchingMachine
open StackMachine StackMachine.Routine
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

def completionPart (extra : Nat) (w : GeneratorWorkspace extra) : Routine (extra+62) :=
  sequence (ofProgram (ListPrograms.copyProgram (extra+61) (w 35) (w 52) (w 59)))
    (sequence (ofProgram (ListPrograms.copyProgram (extra+61) (w 35) (w 53) (w 59)))
      (sequence (ofProgram (ListPrograms.copyProgram (extra+61) (w 49) (w 58) (w 59)))
        (sequence (emitCompletion (extra+49) w.completion) (clearRegisters [w 52,w 53]))))

def completionPartScratch : List (Fin 64) := [40,41,42,43,44,45,46,47,52,53,54,55,58,59]
def completionPartCost (first ports count : Nat) :=
  let bound := 2*first+ports+2*count
  10*first+5*count+count*(320*(bound+1)^3+2)+2*(bound+2)+11

theorem completionPart_executes (extra : Nat) (w : GeneratorWorkspace extra)
    (first ports count : Nat) (store : Fin (extra+64) → List Bool)
    (firstValue : store (w 35)=List.replicate first true) (portsValue : store (w 48)=List.replicate ports true)
    (countValue : store (w 49)=List.replicate count true)
    (empty : ∀ i∈completionPartScratch,store (w i)=[]) :
    ∃ time ≤ completionPartCost first ports count,
      Executes (completionPart extra w) store time
        (Function.update store (w 36) ((Encoding.sequence (Encoding.list Encoding.natural)
          (completionRows first first ports count)).reverse++store (w 36))) := by
  let s1 := Function.update store (w 52) (List.replicate first true)
  let s2 := Function.update s1 (w 53) (List.replicate first true)
  let s3 := Function.update s2 (w 58) (List.replicate count true)
  have a : Executes (ofProgram (ListPrograms.copyProgram (extra+61) (w 35) (w 52) (w 59))) store (5*first+2) s1 := by
    simpa only [firstValue,List.length_replicate,empty 52 (by decide),List.append_nil,s1] using
      copy_executes (extra+61) (w 35) (w 52) (w 59) (by simp [w.injective.eq_iff])
        (by simp [w.injective.eq_iff]) (by simp [w.injective.eq_iff]) store (empty 59 (by decide))
  have b : Executes (ofProgram (ListPrograms.copyProgram (extra+61) (w 35) (w 53) (w 59))) s1 (5*first+2) s2 := by
    have run := copy_executes (extra+61) (w 35) (w 53) (w 59)
      (by simp [w.injective.eq_iff]) (by simp [w.injective.eq_iff]) (by simp [w.injective.eq_iff]) s1
      (by simp [s1,w.injective.eq_iff,empty 59 (by decide)])
    simpa [s2,s1,w.injective.eq_iff,firstValue,empty 53 (by decide)] using run
  have c : Executes (ofProgram (ListPrograms.copyProgram (extra+61) (w 49) (w 58) (w 59))) s2 (5*count+2) s3 := by
    have run := copy_executes (extra+61) (w 49) (w 58) (w 59)
      (by simp [w.injective.eq_iff]) (by simp [w.injective.eq_iff]) (by simp [w.injective.eq_iff]) s2
      (by simp [s2,s1,w.injective.eq_iff,empty 59 (by decide)])
    simpa [s3,s2,s1,w.injective.eq_iff,countValue,empty 58 (by decide)] using run
  let bound := 2*first+ports+2*count
  have readyEmpty (i : Fin 15) (member : i∈([2,3,4,5,7,8,9,10,11,12] : List (Fin 15))) : s3 (w.completion i)=[] := by
    simp only [List.mem_cons,List.not_mem_nil] at member
    rcases member with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|h
    all_goals first | contradiction | simp [GeneratorWorkspace.completion,generatorCompletionPositions,s3,s2,s1,w.injective.eq_iff,empty,completionPartScratch]
  obtain ⟨loopTime,loopBound,looping⟩ := emitCompletion_executes (extra+49) w.completion count bound s3
    (by simp [GeneratorWorkspace.completion,generatorCompletionPositions,s3])
    (by simp [GeneratorWorkspace.completion,generatorCompletionPositions,s3,s2,s1,w.injective.eq_iff,portsValue])
    (by simp [GeneratorWorkspace.completion,generatorCompletionPositions,s3,s2,s1,w.injective.eq_iff,portsValue,bound];omega) readyEmpty
  let s4 := completionResult (extra+49) w.completion s3 count
  have bounded (r : Fin (extra+64)) (member : r∈[w 52,w 53]) : (s4 r).length≤bound := by
    simp only [List.mem_cons,List.not_mem_nil] at member
    rcases member with rfl|rfl|h
    all_goals first | contradiction | (simp [s4,completionResult,GeneratorWorkspace.completion,generatorCompletionPositions,s3,s2,s1,w.injective.eq_iff];dsimp [bound];omega)
  obtain ⟨clearTime,clearBound,clearing⟩ := clearRegisters_selected_executes [w 52,w 53] s4 bound bounded
  have combined := a.sequence (b.sequence (c.sequence (looping.sequence clearing)))
  refine ⟨5*first+2+1+(5*first+2+1+(5*count+2+1+(loopTime+1+clearTime))),?_,?_⟩
  · change clearTime≤2*(bound+2) at clearBound
    dsimp only [completionPartCost]
    change _ ≤ 10*first+5*count+count*(320*(bound+1)^3+2)+2*(bound+2)+11
    omega
  · have final : clearedStore [w 52,w 53] s4=Function.update store (w 36)
        ((Encoding.sequence (Encoding.list Encoding.natural) (completionRows first first ports count)).reverse++store (w 36)) := by
      funext r
      by_cases a0 : r=w 52
      · subst r;simp [clearedStore,w.injective.eq_iff,empty 52 (by decide)]
      · by_cases a1 : r=w 53
        · subst r;simp [clearedStore,w.injective.eq_iff,empty 53 (by decide)]
        · by_cases a2 : r=w 58
          · subst r;simp [clearedStore,s4,completionResult,GeneratorWorkspace.completion,generatorCompletionPositions,s3,s2,s1,w.injective.eq_iff,empty 58 (by decide)]
          · by_cases a3 : r=w 36
            · subst r;simp [clearedStore,s4,completionResult,GeneratorWorkspace.completion,generatorCompletionPositions,s3,s2,s1,w.injective.eq_iff,portsValue]
            · simp [clearedStore,s4,completionResult,GeneratorWorkspace.completion,generatorCompletionPositions,s3,s2,s1,a0,a1,a2,a3]
    simpa only [completionPart,final] using combined

end Counting.External.MatchingMachine
