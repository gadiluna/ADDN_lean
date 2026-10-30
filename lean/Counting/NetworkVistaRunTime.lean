import Counting.StackRealizabilityExternalFields
import Counting.StackDagIncrement
import Counting.StackEncodingFrameStore
import Counting.StackUnframeCanonical
import Counting.StackDagRedBounds

namespace Counting.StackMachine.NetworkVista.Run
open Routine EncodingPrograms RealizabilityCall
set_option backward.isDefEq.respectTransparency false

def reverseExternal (source target : Fin 30) : Routine 128 :=
  ofProgram (ListPrograms.reverseProgram 128 (context source) (context target))

theorem reverseExternal_executes (data : Fin 30→List Bool) (source target : Fin 30)
    (different : source≠target) :
    Executes (reverseExternal source target) (file data) (2*(data source).length+1)
      (file (Function.update (Function.update data source []) target ((data source).reverse++data target))) := by
  have run := reverse_executes 128 (context source) (context target)
    (fun equal=>different (context.injective equal)) (file data)
  rw [file_context,file_context,file_update,file_update] at run
  exact run

def incrementTime : Routine 128 := sequence (ofProgram (unframeProgram 127 100 124 125))
  (sequence (DagValidation.incrementRoutine 127 126 124 125) (frameRoutine 127 124 100 125))

theorem incrementTime_executes (data : Fin 30→List Bool) (time : Nat)
    (encoded : data 0=Encoding.natural.encode time)
    (e24 : data 24=[]) (e25 : data 25=[]) (e26 : data 26=[]) :
    ∃ steps ≤ 20*((data 0).length+1), Executes incrementTime (file data) steps
      (file (Function.update data 0 (Encoding.natural.encode (time+1)))) := by
  have first := unframe_canonical_executes 127 (context 0) (context 24) (context 25)
    (by decide) (by decide) (by decide) (file data) time.bits []
    (by simp [encoded,Encoding.natural]) (by simp [e25])
  rw [file_context,e24,List.append_nil,file_update,file_update] at first
  let a := Function.update (Function.update data 0 []) 24 time.bits
  obtain ⟨s,b,r⟩ := DagValidation.increment_natural 127 (context 26) (context 24) (context 25)
    (by decide) (by decide) (by decide) (file a)
    (by simp [a,e26]) (by simp [a,e25]) time (by simp [a])
  rw [file_update] at r
  let next := Function.update a 24 (time+1).bits
  have last := frame_executes_updates 127 (context 24) (context 0) (context 25)
    (by decide) (by decide) (by decide) (file next) (by simp [next,a,e25])
  rw [file_context,file_context,file_update,file_update] at last
  have input : next 24=(time+1).bits := by simp [next]
  have output : next 0=[] := by simp [next,a]
  rw [input,output,List.append_nil] at last
  have final : Function.update (Function.update next 24 []) 0 (Encoding.frame (time+1).bits)=
      Function.update data 0 (Encoding.natural.encode (time+1)) := by
    funext r
    by_cases n0:r=0 <;> by_cases n24:r=24 <;> simp [next,a,n0,n24,e24,Encoding.natural]
  rw [final] at last
  refine ⟨_,?_,first.sequence (r.sequence last)⟩
  have succBound : (time+1).size≤time.size+1 := by
    simpa only [Machine.increment_bits,Encoding.bits_length] using DagValidation.increment_length_le time.bits
  rw [encoded,Encoding.natural_length]
  simp only [Encoding.bits_length]
  omega

end Counting.StackMachine.NetworkVista.Run
