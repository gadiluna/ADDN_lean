import Counting.StackRealizabilityIncidenceItem

namespace Counting.StackMachine.RealizabilityCheck
open Routine
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

def incomingRowValues (node : Executable.Node) (query : Nat) : Nat → List Bool
  | 0 => []
  | count+1 => decide (0 < Executable.countFrom node query)::incomingRowValues node (query+1) count

def parentRowValues (node : Executable.Node) (query : Nat) : Nat → List Bool
  | 0 => []
  | count+1 => decide (node.parent=some query)::parentRowValues node (query+1) count

@[simp] theorem incomingRowValues_length (node : Executable.Node) (query count : Nat) :
    (incomingRowValues node query count).length=count := by
  induction count generalizing query with
  | zero => rfl
  | succ count ih => simp [incomingRowValues,ih]

@[simp] theorem parentRowValues_length (node : Executable.Node) (query count : Nat) :
    (parentRowValues node query count).length=count := by
  induction count generalizing query with
  | zero => rfl
  | succ count ih => simp [parentRowValues,ih]

theorem incidenceLoop_executes (source index incoming parent statusTail width bits outer : List Bool)
    (query : Nat) (accepted : Bool) (nodes : List Executable.Node) (position : Fin nodes.length)
    (suffix : List Bool) (input : source=Encoding.sequence Encoding.node nodes++suffix)
    (indexAt : index.length=position.val) :
    ∃ time ≤ bits.length*(21000*(source.length+query+bits.length+1)^4+2)+1,
      Executes (forEach 43 incidenceItem)
        (incidenceTableFile source index query.bits incoming parent (accepted::statusTail) width bits outer) time
        (incidenceTableFile source index (query+bits.length).bits
          ((incomingRowValues nodes[position] query bits.length).reverse++incoming)
          ((parentRowValues nodes[position] query bits.length).reverse++parent)
          (accepted::statusTail) width [] outer) := by
  induction bits generalizing query incoming parent with
  | nil =>
    obtain ⟨ran,halted⟩ := repeat_empty (43:Fin 46) incidenceItem
      (incidenceTableFile source index query.bits incoming parent (accepted::statusTail) width [] outer)
      (by simp [incidenceTableFile])
    exact ⟨1,by simp,⟨1,_⟩,ran,halted,by simp [incomingRowValues,parentRowValues]⟩
  | cons bit bits ih =>
    let original := incidenceTableFile source index query.bits incoming parent
      (accepted::statusTail) width (bit::bits) outer
    let consumed := incidenceTableFile source index query.bits incoming parent
      (accepted::statusTail) width bits outer
    let nextIncoming := decide (0 < Executable.countFrom nodes[position] query)::incoming
    let nextParent := decide (nodes[position].parent=some query)::parent
    let middle := incidenceTableFile source index (query+1).bits nextIncoming nextParent
      (accepted::statusTail) width bits outer
    obtain ⟨bodyTime,bodyBound,bodyFinish,bodyRun,bodyHalted,bodyStore⟩ := incidenceItem_executes
      source index incoming parent statusTail width bits outer query accepted nodes position suffix input indexAt
    obtain ⟨tailTime,tailBound,tailFinish,tailRun,tailHalted,tailStore⟩ := ih nextIncoming nextParent (query+1)
    have consumedEq : Function.update original 43 bits=consumed := by
      funext r
      fin_cases r <;> simp [original,consumed,incidenceTableFile]
    have iteration := repeat_iteration (43:Fin 46) incidenceItem original bit bits
      (by simp [original,incidenceTableFile]) bodyTime bodyFinish
      (by simpa only [consumedEq] using bodyRun) bodyHalted
    refine ⟨bodyTime+2+tailTime,?_,tailFinish,?_,tailHalted,?_⟩
    · let S := source.length+query+(bit::bits).length+1
      have qsize : query.size ≤ query := Nat.size_le.mpr Nat.lt_two_pow_self
      have bodyLimit : bodyTime ≤ 21000*S^4 := bodyBound.trans
        (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by dsimp only [S];simp only [List.length_cons];omega) 4))
      have tailSize : source.length+(query+1)+bits.length+1=S := by
        dsimp only [S];simp only [List.length_cons];omega
      rw [tailSize] at tailBound
      change bodyTime+2+tailTime ≤ (bit::bits).length*(21000*S^4+2)+1
      simp only [List.length_cons,Nat.add_mul,Nat.one_mul]
      omega
    · rw [Machine.run_add,iteration,Option.bind_some,bodyStore]
      exact tailRun
    · apply tailStore.trans
      congr 1
      · congr 1; simp only [List.length_cons];omega
      · simp [incomingRowValues,nextIncoming,List.append_assoc]
      · simp [parentRowValues,nextParent,List.append_assoc]

end Counting.StackMachine.RealizabilityCheck
