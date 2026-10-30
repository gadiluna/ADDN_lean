import Counting.StackDagIncrement
import Counting.StackRoutineLists

namespace Counting.StackMachine.AuditPrefix
open Routine
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

abbrev saveAnchor : Routine 50 := sequence (clear 46)
  (sequence (ofProgram (ListPrograms.copyProgram 49 30 46 4))
    (DagValidation.incrementRoutine 49 0 46 4))

/-- Save the current flat level as the canonical optional-natural payload
level+1, preserving the source level. Replacement and carry propagation
are actual charged operations. -/
theorem saveAnchor_executes (store : Store 50) (level : Nat)
    (levelAt : store 30=level.bits) (e0 : store 0=[]) (e4 : store 4=[]) :
    ∃ time ≤ (store 46).length+9*level.size+15,
      Executes saveAnchor store time (Function.update store 46 (level+1).bits) := by
  have a:=clear_executes (46:Fin 52) store
  let cleared:=Function.update store 46 []
  have b:=copy_executes 49 (30:Fin 52) 46 4 (by decide) (by decide) (by decide) cleared
    (by simp [cleared,e4])
  have source : cleared 30=level.bits := by simp [cleared,levelAt]
  have target : cleared 46=[] := by simp [cleared]
  rw [source,target,List.append_nil] at b
  let copied:=Function.update store 46 level.bits
  have bResult : Function.update cleared 46 level.bits=copied := by simp [cleared,copied]
  rw [bResult] at b
  obtain ⟨time,bound,c⟩:=DagValidation.increment_natural 49 (0:Fin 52) 46 4
    (by decide) (by decide) (by decide) copied (by simp [copied,e0]) (by simp [copied,e4])
    level (by simp [copied])
  simp only [copied,Function.update_idem] at c
  refine ⟨_,?_,a.sequence (b.sequence c)⟩
  simp only [Encoding.bits_length]
  omega

abbrev advanceLevel : Routine 50 := sequence (DagValidation.incrementRoutine 49 0 41 4)
  (DagValidation.incrementRoutine 49 0 30 4)

theorem advanceLevel_executes (store : Store 50) (level : Nat)
    (levelAt : store 41=level.bits) (childAt : store 30=(level+1).bits)
    (e0 : store 0=[]) (e4 : store 4=[]) :
    ∃ time ≤ 4*level.size+4*(level+1).size+15,
      Executes advanceLevel store time
        (Function.update (Function.update store 41 (level+1).bits) 30 (level+1+1).bits) := by
  obtain ⟨firstTime,firstBound,a⟩:=DagValidation.increment_natural 49 (0:Fin 52) 41 4
    (by decide) (by decide) (by decide) store e0 e4 level levelAt
  let advanced:=Function.update store 41 (level+1).bits
  obtain ⟨secondTime,secondBound,b⟩:=DagValidation.increment_natural 49 (0:Fin 52) 30 4
    (by decide) (by decide) (by decide) advanced (by simp [advanced,e0]) (by simp [advanced,e4])
    (level+1) (by simp [advanced,childAt])
  exact ⟨_,by omega,a.sequence b⟩

end Counting.StackMachine.AuditPrefix
