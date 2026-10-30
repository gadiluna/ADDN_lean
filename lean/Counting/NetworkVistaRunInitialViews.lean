import Counting.NetworkVistaInitial
import Counting.StackRealizabilityExternalFields
import Counting.StackRoutineRelocate

namespace Counting.StackMachine.NetworkVista.Run
open Routine EncodingPrograms RealizabilityCall
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

/-- The initializer consumes a private copy of the leader array and leaves
the immutable leader array available to every receiver. -/
def initialRoles : Fin 21 ↪ Fin 130 :=
  ⟨![122,115,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,123,18,19,102],by decide⟩

def initializeViews : Routine 128 :=
  sequence (copyExternal 1 23)
    (sequence (pushBit (context 15) true) (relocate initialPrefix initialRoles))

def initializedViews (data : Fin 30→List Bool) (leaders : Array Bool) : Fin 30→List Bool :=
  Function.update (Function.update (Function.update data 15 [true])
    22 (List.replicate leaders.size true))
    2 ((Encoding.array Encoding.vista).encode (leaders.map Executable.initialVista))

theorem initializeViews_executes (data : Fin 30→List Bool) (leaders : Array Bool)
    (encoded : data 1=(Encoding.array Encoding.boolean).encode leaders)
    (e2 : data 2=[]) (e15 : data 15=[]) (e22 : data 22=[]) (e23 : data 23=[]) :
    ∃ time ≤ 2010*((data 1).length+1)^3,
      Executes initializeViews (file data) time (file (initializedViews data leaders)) := by
  have copied := copyExternal_executes data 1 23 (by decide)
  rw [e23,List.append_nil] at copied
  let a := Function.update data 23 (data 1)
  have flag := pushBit_executes (context 15) true (file a)
  rw [file_context,show a 15=[] by simp [a,e15],file_update] at flag
  let b := Function.update a 15 [true]
  obtain ⟨time,bound,run⟩ := initialPrefix_executes (file b ∘ initialRoles) true []
    (by simp [b,initialRoles,file])
    (by
      intro r small different
      fin_cases r <;> simp_all [initialRoles,file,b,a])
    (by simp [initialRoles,file]) (by simp [initialRoles,file])
    (by simp [initialRoles,b,a,e2,file]) leaders.toList []
    (by simp [initialRoles,b,a,encoded,Encoding.array,Encoding.transport,file])
  have relocated : Executes (relocate initialPrefix initialRoles) (file b) time
      (file (initializedViews data leaders)) := by
    apply relocate_executes_frame initialPrefix initialRoles (file b)
      (file (initializedViews data leaders)) (file b ∘ initialRoles)
      (initialPrefixStore (file b ∘ initialRoles) leaders.toList []) time rfl
    · intro r
      fin_cases r <;>
        simp [initialPrefixStore,initialRoles,initializedViews,b,a,e23,
          Encoding.array,Encoding.transport,file]
    · intro r outside
      have n122 : r≠context 22 := by simpa [initialRoles,context] using (outside 0).symm
      have n123 : r≠context 23 := by simpa [initialRoles,context] using (outside 17).symm
      have n102 : r≠context 2 := by simpa [initialRoles,context] using (outside 20).symm
      rw [show file (initializedViews data leaders)=
        Function.update (Function.update (Function.update (file b) (context 23) [])
          (context 22) (List.replicate leaders.size true))
          (context 2) ((Encoding.array Encoding.vista).encode (leaders.map Executable.initialVista)) by
            rw [file_update,file_update,file_update]
            congr 1
            funext i
            fin_cases i <;> simp [initializedViews,b,a,e23]]
      simp [n122,n123,n102]
    · exact run
  have source : (file b ∘ initialRoles) 17=data 1 := by simp [initialRoles,b,a,file]
  rw [source] at bound
  have linear : (data 1).length+1≤((data 1).length+1)^3 := Nat.le_self_pow (by decide) _
  refine ⟨_,?_,copied.sequence (flag.sequence relocated)⟩
  omega

end Counting.StackMachine.NetworkVista.Run
