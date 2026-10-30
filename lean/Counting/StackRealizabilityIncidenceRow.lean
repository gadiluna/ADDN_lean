import Counting.StackRealizabilityIncidenceLoop

namespace Counting.StackMachine.RealizabilityCheck
open Routine
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

/-- Query every explicit sender column, including the outside slot when the
caller supplies width = node count + 1. -/
def incidenceRow : Routine 44 := sequence (ofProgram (ListPrograms.copyProgram 43 42 43 0))
  (sequence (forEach 43 incidenceItem)
    (sequence (clear 21) (pushBit 36 true)))

theorem incidenceRow_executes (source index incoming parent statusTail width outer : List Bool)
    (accepted : Bool) (nodes : List Executable.Node) (position : Fin nodes.length)
    (suffix : List Bool) (input : source=Encoding.sequence Encoding.node nodes++suffix)
    (indexAt : index.length=position.val) :
    ∃ time ≤ 30000*(source.length+width.length+1)^6,
      Executes incidenceRow
        (incidenceTableFile source index [] incoming parent (accepted::statusTail) width [] outer) time
        (incidenceTableFile source (true::index) []
          ((incomingRowValues nodes[position] 0 width.length).reverse++incoming)
          ((parentRowValues nodes[position] 0 width.length).reverse++parent)
          (accepted::statusTail) width [] outer) := by
  let original := incidenceTableFile source index [] incoming parent (accepted::statusTail) width [] outer
  have copying := copy_executes 43 42 43 0 (by decide) (by decide) (by decide) original
    (by simp [original,incidenceTableFile,incidenceFile])
  have w42 : original 42=width := by simp [original,incidenceTableFile]
  have w43 : original 43=[] := by simp [original,incidenceTableFile]
  rw [w42,w43,List.append_nil] at copying
  have copied : Function.update original 43 width=
      incidenceTableFile source index [] incoming parent (accepted::statusTail) width width outer := by
    funext r
    fin_cases r <;> simp [original,incidenceTableFile,incidenceFile]
  rw [copied] at copying
  obtain ⟨loopTime,loopBound,looping⟩ := incidenceLoop_executes source index incoming parent statusTail
    width width outer 0 accepted nodes position suffix input indexAt
  simp only [Nat.zero_bits,Nat.zero_add,Nat.add_zero] at looping loopBound
  let middle := incidenceTableFile source index width.length.bits
    ((incomingRowValues nodes[position] 0 width.length).reverse++incoming)
    ((parentRowValues nodes[position] 0 width.length).reverse++parent) (accepted::statusTail) width [] outer
  have clearing := clear_executes (21:Fin 46) middle
  have m21 : middle 21=width.length.bits := by simp [middle,incidenceTableFile,incidenceFile]
  rw [m21,Encoding.bits_length] at clearing
  let cleared := Function.update middle 21 []
  have pushIndex := pushBit_executes (36:Fin 46) true cleared
  have final : Function.update cleared 36 (true::cleared 36) =
      incidenceTableFile source (true::index) []
        ((incomingRowValues nodes[position] 0 width.length).reverse++incoming)
        ((parentRowValues nodes[position] 0 width.length).reverse++parent)
        (accepted::statusTail) width [] outer := by
    funext r
    fin_cases r <;> simp [cleared,middle,incidenceTableFile,incidenceFile]
  rw [final] at pushIndex
  have execution := copying.sequence (looping.sequence (clearing.sequence pushIndex))
  let S := source.length+width.length+1
  have widthBound : width.length ≤ S := by dsimp only [S];omega
  have loops : loopTime ≤ 21000*S^5+2*S+1 := by
    apply loopBound.trans
    calc width.length*(21000*S^4+2)+1 ≤ S*(21000*S^4+2)+1 := by gcongr
         _ = _ := by ring
  have power : S^5 ≤ S^6 := Nat.pow_le_pow_right (by dsimp only [S];omega) (by decide)
  have linear : S ≤ S^6 := Nat.le_self_pow (by decide) _
  have one : 1 ≤ S^6 := Nat.one_le_pow _ _ (by dsimp only [S];omega)
  have size : width.length.size ≤ width.length := Nat.size_le.mpr Nat.lt_two_pow_self
  exact ⟨_,by change _ ≤ 30000*S^6;omega,execution⟩

end Counting.StackMachine.RealizabilityCheck
