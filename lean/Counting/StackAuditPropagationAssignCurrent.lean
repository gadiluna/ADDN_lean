import Counting.StackAuditPropagationAssign
import Counting.StackRoutineLists
import Counting.StackRoutineBasic

namespace Counting.StackMachine.AuditPropagation
open Routine EncodingPrograms
set_option backward.isDefEq.respectTransparency false

/-- Materialize the one-based field index from the bounded physical node
counter, then consume and assign precisely one anchor value. -/
abbrev assignCurrent : Routine 35 := sequence (ofProgram (ListPrograms.copyProgram 34 18 31 4))
  (sequence (pushBit 31 true) assignNode)

theorem assignCurrent_executes (store : Store 35) (weights : Array Nat) (index value : Nat)
    (inside : index<weights.size) (suffix : List Bool)
    (source : store 36=Encoding.natural.encode value++suffix)
    (array : store 35=(Encoding.array Encoding.natural).encode weights)
    (counter : store 18=List.replicate index true)
    (e2 : store 2=[]) (e3 : store 3=[]) (e4 : store 4=[]) (e21 : store 21=[]) (e31 : store 31=[]) :
    ∃ time ≤ 5*(store 35).length+8*index+22*value.size+32,
      Executes assignCurrent store time
        (Function.update (Function.update store 36 suffix) 35
          ((Encoding.array Encoding.natural).encode (weights.setIfInBounds index value))) := by
  have copied := copy_executes 34 (18:Fin 37) 31 4
    (by decide) (by decide) (by decide) store e4
  rw [counter,e31,List.append_nil,List.length_replicate] at copied
  let first := Function.update store 31 (List.replicate index true)
  have pushed := pushBit_executes (31:Fin 37) true first
  have ready : Function.update first 31 (true::first 31)=
      Function.update store 31 (List.replicate (index+1) true) := by
    simp [first,List.replicate_succ]
  rw [ready] at pushed
  let prepared := Function.update store 31 (List.replicate (index+1) true)
  obtain ⟨time,bounded,assigned⟩ := assignNode_executes prepared weights index value inside suffix
    (by simpa [prepared] using source) (by simpa [prepared] using array) (by simp [prepared])
    (by simp [prepared,e2]) (by simp [prepared,e3]) (by simp [prepared,e4]) (by simp [prepared,e21])
  have finish : Function.update (Function.update (Function.update prepared 36 suffix) 31 []) 35
      ((Encoding.array Encoding.natural).encode (weights.setIfInBounds index value))=
      Function.update (Function.update store 36 suffix) 35
        ((Encoding.array Encoding.natural).encode (weights.setIfInBounds index value)) := by
    funext r
    by_cases a : r=31 <;> by_cases b : r=35 <;> by_cases c : r=36 <;> simp [prepared,a,b,c,e31]
  rw [finish] at assigned
  refine ⟨_,?_,copied.sequence (pushed.sequence assigned)⟩
  have sameArray : prepared 35=store 35 := by simp [prepared]
  rw [sameArray] at bounded
  omega

end Counting.StackMachine.AuditPropagation
