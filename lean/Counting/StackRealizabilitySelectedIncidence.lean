import Counting.StackRealizabilityIncidenceRead

namespace Counting.StackMachine.RealizabilityCheck
open Routine
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

/-- Read the receiver from the preserved serialized node sequence, and append
both actual incidence bits. The query register is a binary DAG index. -/
def selectedIncidence : Routine 40 := sequence incidenceRead
  (sequence incidenceBody (ofProgram (ListPrograms.reverseProgram 40 32 37)))

theorem selectedIncidence_executes (source index incoming parent : List Bool)
    (query : Nat) (accepted : Bool) (tail : List Bool) (nodes : List Executable.Node)
    (position : Fin nodes.length) (suffix : List Bool)
    (input : source = Encoding.sequence Encoding.node nodes ++ suffix)
    (indexAt : index.length = position.val) :
    ∃ time ≤ 20000*(source.length+query.size+1)^4,
      Executes selectedIncidence
        (incidenceFile source index query.bits incoming parent (accepted::tail)) time
        (incidenceFile source index query.bits
          (decide (0 < Executable.countFrom nodes[position] query)::incoming)
          (decide (nodes[position].parent = some query)::parent) (accepted::tail)) := by
  let original := incidenceFile source index query.bits incoming parent (accepted::tail)
  let read := Function.update original 0 (Encoding.node.encode nodes[position])
  obtain ⟨readTime,readBound,reading⟩ := incidenceRead_executes source index query.bits incoming parent
    accepted tail nodes position suffix input indexAt
  obtain ⟨bodyTime,bodyBound,bodyRun⟩ := nodeIncidence_executes nodes[position] query [] incoming
  simp only [List.append_nil,List.length_nil,Nat.add_zero] at bodyBound bodyRun
  let incomingBit := decide (0 < Executable.countFrom nodes[position] query)
  let parentBit := decide (nodes[position].parent = some query)
  let checked := Function.update (Function.update original 22 (incomingBit::incoming)) 32 [parentBit]
  have checking : Executes incidenceBody read bodyTime checked := by
    apply relocate_executes_frame nodeIncidence incidenceBodyRoles read checked
      (AnchorCoefficient.file (Encoding.node.encode nodes[position]) query.bits incoming [] [] [] [] [] [] [])
      _ bodyTime _ _ _ bodyRun
    · funext r
      fin_cases r <;> simp [read,original,incidenceFile,incidenceBodyRoles,AnchorCoefficient.file]
    · intro r
      fin_cases r <;> simp [checked,original,incidenceFile,incidenceBodyRoles,AnchorCoefficient.file,
        incomingBit,parentBit]
    · intro r outside
      have n0 : r ≠ 0 := by intro same;subst r;exact outside 0 rfl
      have n22 : r ≠ 22 := by intro same;subst r;exact outside 22 rfl
      have n32 : r ≠ 32 := by intro same;subst r;exact outside 32 rfl
      simp [checked,read,n0,n22,n32]
  have reversing := reverse_executes 40 32 37 (by decide) checked
  have at32 : checked 32 = [parentBit] := by simp [checked]
  have at37 : checked 37 = parent := by simp [checked,original,incidenceFile]
  rw [at32,at37] at reversing
  simp only [List.length_cons,List.length_nil,List.reverse_cons,List.reverse_nil,
    List.nil_append,List.singleton_append] at reversing
  have final : Function.update (Function.update checked 32 []) 37 (parentBit::parent) =
      incidenceFile source index query.bits (incomingBit::incoming) (parentBit::parent) (accepted::tail) := by
    funext r
    fin_cases r <;> simp [checked,original,incidenceFile]
  rw [final] at reversing
  have member := DagValidation.node_sequence_member_le nodes nodes[position]
    (List.getElem_mem position.isLt)
  have nodeBound : (Encoding.node.encode nodes[position]).length ≤ source.length := by
    rw [input,List.length_append]
    omega
  let S := source.length+query.size+1
  have readLimit : readTime ≤ 7000*S^4 := readBound.trans
    (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by dsimp only [S];omega) 4))
  have bodyLimit : bodyTime ≤ 8000*S^4 := by
    apply bodyBound.trans
    apply Nat.mul_le_mul_left
    exact (Nat.pow_le_pow_left (by dsimp only [S];omega) 3).trans
      (Nat.pow_le_pow_right (by dsimp only [S];omega) (by decide))
  have one : 1 ≤ S^4 := Nat.one_le_pow _ _ (by dsimp only [S];omega)
  have execution := reading.sequence (checking.sequence reversing)
  exact ⟨_,by change _ ≤ 20000*S^4;omega,execution⟩

end Counting.StackMachine.RealizabilityCheck
