import Counting.StackRoutineUnary
import Counting.StackEncodingFrameStore

namespace Counting.StackMachine.AuditDescendant
open Routine EncodingPrograms
set_option backward.isDefEq.respectTransparency false

/-- Build the canonical weight query from the structural outer-loop index.
The index itself survives; the temporary unary copy is consumed. -/
def prepareQuery : Routine 46 := sequence (ofProgram (ListPrograms.copyProgram 45 43 18 0))
  (sequence (ofProgram (Unary.toBinaryProgram 45 18 31 0)) (frameRoutine 45 31 33 0))

theorem prepareQuery_executes (store : Store 46)
    (e0 : store 0=[]) (e18 : store 18=[]) (e31 : store 31=[]) (e33 : store 33=[]) :
    ∃ time ≤ 20*((store 43).length+1)^2,
      Executes prepareQuery store time
        (Function.update store 33 (Encoding.natural.encode (store 43).length)) := by
  have a:=copy_executes 45 (43:Fin 48) 18 0 (by decide) (by decide) (by decide) store e0
  rw [e18,List.append_nil] at a
  let copied:=Function.update store 18 (store 43)
  obtain ⟨binaryTime,binaryBound,b⟩:=toBinary_executes 45 (18:Fin 48) 31 0
    (by decide) (by decide) (by decide) copied 0
    (by simpa [copied] using e31) (by simp [copied,e0])
  have count : copied 18=store 43 := by simp [copied]
  rw [count,Nat.zero_add] at b
  rw [count] at binaryBound
  let converted:=Function.update store 31 (store 43).length.bits
  have restored : Function.update (Function.update copied 18 []) 31 (store 43).length.bits=converted := by
    simp only [copied,Function.update_idem]
    rw [←e18,Function.update_eq_self]
  rw [restored] at b
  have c:=frame_executes_updates 45 (31:Fin 48) 33 0 (by decide) (by decide) (by decide)
    converted (by simp [converted,e0])
  have value : converted 31=(store 43).length.bits := by simp [converted]
  have output : converted 33=[] := by simp [converted,e33]
  rw [value,output,List.append_nil,Encoding.bits_length] at c
  have final : Function.update (Function.update converted 31 []) 33
      (Encoding.frame (store 43).length.bits)=
      Function.update store 33 (Encoding.natural.encode (store 43).length) := by
    simp only [converted,Function.update_idem]
    rw [←e31,Function.update_eq_self]
    rfl
  rw [final] at c
  have width : (store 43).length.size ≤ (store 43).length:=Nat.size_le.mpr Nat.lt_two_pow_self
  refine ⟨_,?_,a.sequence (b.sequence c)⟩
  change 5*(store 43).length+2+1+(binaryTime+1+(5*(store 43).length.size+4)) ≤
    20*((store 43).length+1)^2
  nlinarith only [binaryBound,width]

end Counting.StackMachine.AuditDescendant
