import Counting.StackDagCanonicalInitializeCount
import Counting.StackRepeatBit
import Counting.StackEmitNatural

namespace Counting.StackMachine.DagUpdate.Canonical
open Routine EncodingPrograms RealizabilityCall
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

theorem zeroMapping_payload (n : Nat) :
    Encoding.sequence Encoding.natural (List.replicate n 0)=List.replicate n false := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [List.replicate_succ,Encoding.sequence,ih]
    rfl

def initializeMappingRoles : PowerWorkspace 125 := ⟨![123,101,0,1,2],by decide⟩

def initializeMapping : Routine 128 := sequence (copyExternal 23 26)
  (sequence (repeatBit (context 26) (context 1) false)
    (sequence (emitNatural 125 initializeMappingRoles)
      (sequence (pushBit (context 2) false) (clearExternal 4))))

def initializeMappingData (data : Fin 30→List Bool) (n : Nat) : Fin 30→List Bool :=
  Function.update (Function.update (Function.update data
    1 ((Encoding.array Encoding.natural).encode (Array.replicate n 0)))
    2 ((Encoding.array Encoding.node).encode #[])) 4 []

theorem initializeMapping_executes (data : Fin 30→List Bool) (n : Nat)
    (count : data 23=List.replicate n true) (flag : data 4=[true])
    (e1 : data 1=[]) (e2 : data 2=[]) (e26 : data 26=[]) :
    ∃ time ≤ 40*(n+1)^2,
      Executes initializeMapping (file data) time (file (initializeMappingData data n)) := by
  have copied := copyExternal_executes data 23 26 (by decide)
  rw [count,e26,List.append_nil,List.length_replicate] at copied
  let a := Function.update data 26 (List.replicate n true)
  have repeated := repeatBit_executes (context 26) (context 1) false (by decide) (file a)
  rw [file_context,file_context,show a 26=List.replicate n true by simp [a],
    show a 1=[] by simp [a,e1],List.length_replicate,List.append_nil,file_update,file_update] at repeated
  let b := Function.update (Function.update a 26 []) 1 (List.replicate n false)
  obtain ⟨te,be,re⟩ := emitNatural_executes 125 initializeMappingRoles (file b)
    (by simp [initializeMappingRoles,file]) (by simp [initializeMappingRoles,file])
    (by simp [initializeMappingRoles,file])
  have counter : file b (initializeMappingRoles 0)=List.replicate n true := by
    simp [initializeMappingRoles,file,b,a,count]
  rw [counter,List.length_replicate] at be re
  have target : file b (initializeMappingRoles 1)=List.replicate n false := by
    simp [initializeMappingRoles,file,b]
  rw [target] at re
  have encoding : Encoding.natural.encode n++List.replicate n false=
      (Encoding.array Encoding.natural).encode (Array.replicate n 0) := by
    simp [Encoding.array,Encoding.transport,Encoding.list,zeroMapping_payload]
  rw [encoding] at re
  change Executes (emitNatural 125 initializeMappingRoles) (file b) te
    (Function.update (file b) (context 1) ((Encoding.array Encoding.natural).encode (Array.replicate n 0))) at re
  rw [file_update] at re
  let c := Function.update b 1 ((Encoding.array Encoding.natural).encode (Array.replicate n 0))
  have pool := pushBit_executes (context 2) false (file c)
  rw [file_context,show c 2=[] by simp [c,b,a,e2],file_update] at pool
  let d := Function.update c 2 [false]
  have cleared := clearExternal_executes d 4
  rw [show d 4=[true] by simp [d,c,b,a,flag],List.length_singleton] at cleared
  have final : Function.update d 4 []=initializeMappingData data n := by
    funext r
    fin_cases r <;> simp [initializeMappingData,d,c,b,a,e26,Encoding.array,Encoding.transport,
      Encoding.list,Encoding.natural,Encoding.sequence,Encoding.frame]
  rw [final] at cleared
  refine ⟨_,?_,copied.sequence (repeated.sequence (re.sequence (pool.sequence cleared)))⟩
  nlinarith only [be]

end Counting.StackMachine.DagUpdate.Canonical
