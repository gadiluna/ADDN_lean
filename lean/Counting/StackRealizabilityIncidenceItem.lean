import Counting.StackRealizabilitySelectedIncidence

namespace Counting.StackMachine.RealizabilityCheck
open Routine
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

/-- Extra registers contain only explicit loop counters; no receiver is supplied
as a mathematical oracle to the routine. -/
def incidenceTableFile (source index query incoming parent status width inner outer : List Bool) : Store 44 :=
  fun r => if inside : r.val < 42 then
    incidenceFile source index query incoming parent status ⟨r.val,inside⟩
    else if r=42 then width else if r=43 then inner else if r=44 then outer else []

def incidenceSelectedRoles : Fin 42 ↪ Fin 46 where
  toFun r := ⟨r.val,by omega⟩
  inj' := by intro a b same;apply Fin.ext;exact congrArg (fun r : Fin 46 => r.val) same

def incidenceSelected : Routine 44 := mapRegisters incidenceSelectedRoles selectedIncidence

def incidenceItem : Routine 44 := sequence incidenceSelected
  (DagValidation.incrementRoutine 43 0 21 1)

theorem incidenceSelected_executes (source index incoming parent statusTail width inner outer : List Bool)
    (query : Nat) (accepted : Bool) (nodes : List Executable.Node) (position : Fin nodes.length)
    (suffix : List Bool) (input : source=Encoding.sequence Encoding.node nodes++suffix)
    (indexAt : index.length=position.val) :
    ∃ time ≤ 20000*(source.length+query.size+1)^4,
      Executes incidenceSelected
        (incidenceTableFile source index query.bits incoming parent (accepted::statusTail) width inner outer) time
        (incidenceTableFile source index query.bits
          (decide (0 < Executable.countFrom nodes[position] query)::incoming)
          (decide (nodes[position].parent=some query)::parent) (accepted::statusTail) width inner outer) := by
  obtain ⟨time,bound,run⟩ := selectedIncidence_executes source index incoming parent query accepted
    statusTail nodes position suffix input indexAt
  refine ⟨time,bound,?_⟩
  apply relocate_executes_frame selectedIncidence incidenceSelectedRoles _ _ _ _ time _ _ _ run
  · funext r
    simp [incidenceTableFile,incidenceSelectedRoles]
  · intro r
    simp [incidenceTableFile,incidenceSelectedRoles]
  · intro r outside
    have lower : ¬r.val < 42 := by
      intro inside
      exact outside ⟨r.val,inside⟩ (Fin.ext rfl)
    simp [incidenceTableFile,lower]

theorem incidenceItem_executes (source index incoming parent statusTail width inner outer : List Bool)
    (query : Nat) (accepted : Bool) (nodes : List Executable.Node) (position : Fin nodes.length)
    (suffix : List Bool) (input : source=Encoding.sequence Encoding.node nodes++suffix)
    (indexAt : index.length=position.val) :
    ∃ time ≤ 21000*(source.length+query.size+1)^4,
      Executes incidenceItem
        (incidenceTableFile source index query.bits incoming parent (accepted::statusTail) width inner outer) time
        (incidenceTableFile source index (query+1).bits
          (decide (0 < Executable.countFrom nodes[position] query)::incoming)
          (decide (nodes[position].parent=some query)::parent) (accepted::statusTail) width inner outer) := by
  obtain ⟨selectedTime,selectedBound,selecting⟩ := incidenceSelected_executes source index incoming parent
    statusTail width inner outer query accepted nodes position suffix input indexAt
  let middle := incidenceTableFile source index query.bits
    (decide (0 < Executable.countFrom nodes[position] query)::incoming)
    (decide (nodes[position].parent=some query)::parent) (accepted::statusTail) width inner outer
  obtain ⟨incrementTime,incrementBound,incrementing⟩ := DagValidation.increment_natural 43 0 21 1
    (by decide) (by decide) (by decide) middle
    (by simp [middle,incidenceTableFile,incidenceFile]) (by simp [middle,incidenceTableFile,incidenceFile])
    query (by simp [middle,incidenceTableFile,incidenceFile])
  have final : Function.update middle 21 (query+1).bits =
      incidenceTableFile source index (query+1).bits
        (decide (0 < Executable.countFrom nodes[position] query)::incoming)
        (decide (nodes[position].parent=some query)::parent) (accepted::statusTail) width inner outer := by
    funext r
    fin_cases r <;> simp [middle,incidenceTableFile,incidenceFile]
  rw [final] at incrementing
  let S := source.length+query.size+1
  have linear : S ≤ S^4 := Nat.le_self_pow (by decide) _
  have one : 1 ≤ S^4 := Nat.one_le_pow _ _ (by dsimp only [S];omega)
  have execution := selecting.sequence incrementing
  exact ⟨_,by change _ ≤ 21000*S^4;dsimp only [S] at linear one ⊢;omega,execution⟩

end Counting.StackMachine.RealizabilityCheck
