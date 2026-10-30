import Counting.StackRealizabilityRoundFile
import Counting.StackRealizabilityIncidenceSpec

namespace Counting.StackMachine.RealizabilityCheck
open Routine
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2800000

def roundIncidenceRoles : Fin 46 ↪ Fin 100 := ⟨![95,94,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,85,86,36,37,38,39,40,41,78,43,44,45],by decide⟩
def roundIncidenceBody : Routine 98 := mapRegisters roundIncidenceRoles incidenceMatrix

def roundIncidenceData (data : Fin 20→List Bool) (nodes : List Executable.Node) : Fin 20→List Bool :=
  Function.update (Function.update data 14 (parentMatrixValues nodes)) 15 (incomingMatrixValues nodes)

theorem roundIncidenceFile (data : Fin 20→List Bool) (nodes : List Executable.Node) :
    roundFile (roundIncidenceData data nodes)=
      Function.update (Function.update (roundFile data) 94 (parentMatrixValues nodes)) 95 (incomingMatrixValues nodes) := by
  change _=Function.update (Function.update (roundFile data) (roundContext 14) _) (roundContext 15) _
  rw [roundFile_update,roundFile_update]
  rfl

theorem roundIncidenceBody_executes (data : Fin 20→List Bool) (nodes : List Executable.Node)
    (width : List Bool) (accepted : Bool) (tail : List Bool)
    (status : data 5=accepted::tail) (input : data 6=Encoding.sequence Encoding.node nodes)
    (counted : width.length=nodes.length) (e14 : data 14=[]) (e15 : data 15=[]) :
    ∃ time ≤ 40000*((data 6).length+width.length+2)^8,
      Executes roundIncidenceBody (Function.update (roundFile data) 78 width) time
        (Function.update (roundFile (roundIncidenceData data nodes)) 78 (false::width)) := by
  obtain ⟨time,bound,run⟩ := incidenceMatrix_executes nodes (data 6) width accepted tail []
    (by simp [input]) counted
  refine ⟨time,bound,?_⟩
  apply relocate_executes_frame incidenceMatrix roundIncidenceRoles _ _ _ _ time _ _ _ run
  · funext r
    fin_cases r <;> simp [roundFile,roundIncidenceRoles,incidenceTableFile,incidenceFile,status,e14,e15]
  · intro r
    fin_cases r <;> simp [roundFile,roundIncidenceRoles,incidenceTableFile,incidenceFile,roundIncidenceData,status]
  · intro r outside
    have n78 : r≠78 := by intro same;subst r;exact outside 42 rfl
    have n94 : r≠94 := by intro same;subst r;exact outside 1 rfl
    have n95 : r≠95 := by intro same;subst r;exact outside 0 rfl
    rw [roundIncidenceFile]
    simp [n78,n94,n95]

def roundIncidences : Routine 98 := sequence (ofProgram (ListPrograms.copyProgram 97 87 78 0))
  (sequence (discardBit 78) (sequence roundIncidenceBody (clear 78)))

theorem roundIncidences_executes (data : Fin 20→List Bool) (nodes : List Executable.Node)
    (accepted : Bool) (tail : List Bool) (status : data 5=accepted::tail)
    (input : data 6=Encoding.sequence Encoding.node nodes)
    (counted : (data 7).length=nodes.length+1) (e14 : data 14=[]) (e15 : data 15=[]) :
    ∃ time ≤ 50000*((data 6).length+(data 7).length+2)^8,
      Executes roundIncidences (roundFile data) time (roundFile (roundIncidenceData data nodes)) := by
  have copying := copy_executes 97 87 78 0 (by decide) (by decide) (by decide) (roundFile data)
    (by simp [roundFile])
  have sourceAt : roundFile data 87=data 7 := by simp [roundFile]
  have counterAt : roundFile data 78=[] := by simp [roundFile]
  rw [sourceAt,counterAt,List.append_nil] at copying
  let copied := Function.update (roundFile data) 78 (data 7)
  have discarding := discardBit_executes (78:Fin 100) copied
  have copiedAt : copied 78=data 7 := by simp [copied]
  rw [copiedAt] at discarding
  simp only [copied,Function.update_idem] at discarding
  obtain ⟨bodyTime,bodyBound,bodyRun⟩ := roundIncidenceBody_executes data nodes (data 7).tail accepted tail
    status input (by simp [counted]) e14 e15
  let completed := Function.update (roundFile (roundIncidenceData data nodes)) 78 (false::(data 7).tail)
  have clearing := clear_executes (78:Fin 100) completed
  have completedAt : completed 78=false::(data 7).tail := by simp [completed]
  rw [completedAt,List.length_cons,List.length_tail] at clearing
  have final : Function.update completed 78 []=roundFile (roundIncidenceData data nodes) := by
    simp [completed,roundFile]
  rw [final] at clearing
  let S := (data 6).length+(data 7).length+2
  have small : (data 6).length+(data 7).tail.length+2 ≤ S := by simp only [List.length_tail];dsimp only [S];omega
  have bodyLimit := bodyBound.trans (Nat.mul_le_mul_left 40000 (Nat.pow_le_pow_left small 8))
  have widthSmall : (data 7).length ≤ S := by dsimp only [S];omega
  have linear : S ≤ S^8 := Nat.le_self_pow (by decide) _
  have one : 1 ≤ S^8 := Nat.one_le_pow _ _ (by dsimp only [S];omega)
  have execution := copying.sequence (discarding.sequence (bodyRun.sequence clearing))
  exact ⟨_,by change _ ≤ 50000*S^8;omega,execution⟩

end Counting.StackMachine.RealizabilityCheck
