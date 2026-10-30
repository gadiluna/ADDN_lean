import Counting.StackAnchorMatrixInput
import Counting.StackAnchorMatrixOutput
import Counting.StackAnchorMatrixPolynomial
import Counting.StackGaussianNormalInput

namespace Counting.StackMachine.AnchorMatrix
set_option maxHeartbeats 2000000
open Routine
set_option backward.isDefEq.respectTransparency false

abbrev complete : Routine 48 := sequence prepareInput (sequence buildRows emitInput)

def outputWord (anchor leaders : Nat) (vista : Executable.Vista) : List Bool :=
  GaussianNormal.inputWord (Executable.levelNodes vista anchor).length
    (GaussianNormalMatrix.equationMatrix (Executable.levelNodes vista anchor).length (Executable.anchorRows vista anchor leaders))

theorem outputWord_eq (anchor leaders : Nat) (vista : Executable.Vista) :
    outputWord anchor leaders vista=
      Encoding.frame (List.replicate (AnchorCoefficient.selectedNodes vista.nodes.toList anchor).length true)++
        Encoding.rationalMatrix.encode (producedRows vista.nodes.toList anchor (anchor-1) leaders) := by
  rw [producedRows_vista,AnchorCoefficient.matrix_eq_anchorRows]
  simp [outputWord,GaussianNormal.inputWord,AnchorCoefficient.selectedNodes_eq]

/-- Size of the actual serialized solver input produced from the DAG. -/
theorem outputWord_length (anchor leaders : Nat) (vista : Executable.Vista) :
    (outputWord anchor leaders vista).length ≤ 10007*((inputWord anchor leaders vista).length+1)^3 := by
  let nodes := vista.nodes.toList
  let limit := (Encoding.sequence Encoding.node nodes).length
  have matrixBound := matrix_length nodes anchor (anchor-1) leaders limit (by rfl)
  have count := AnchorRow.nodes_length nodes
  have width : (AnchorCoefficient.selectedNodes nodes anchor).length ≤ nodes.length := by
    simpa only [AnchorCoefficient.selectedNodes] using List.length_filter_le (fun node=>node.level==anchor) nodes
  have inputBound : limit+leaders.size+1 ≤ (inputWord anchor leaders vista).length+1 := by
    simp only [inputWord,Encoding.vista,Encoding.transport,Encoding.product,Encoding.list,
      List.length_append,Encoding.natural_length]
    dsimp only [limit,nodes]
    omega
  have raised := matrixBound.trans (Nat.mul_le_mul_left 10004 (Nat.pow_le_pow_left inputBound 3))
  have linear : (inputWord anchor leaders vista).length+1 ≤ ((inputWord anchor leaders vista).length+1)^3 :=
    Nat.le_self_pow (by decide) _
  rw [outputWord_eq,List.length_append,Encoding.frame_length,List.length_replicate]
  dsimp only [limit] at inputBound
  dsimp only [nodes] at count width raised inputBound
  omega

/-- Every operation from serialized DAG input to the exact solver input is
executed: parsing, binary predecessor, repeated scans, arithmetic, list
headers, width framing and full workspace cleanup. -/
theorem complete_executes (anchor leaders : Nat) (vista : Executable.Vista) :
    ∃ time ≤ 7000000000*((inputWord anchor leaders vista).length+1)^6,
      Executes complete (inputFile (inputWord anchor leaders vista) [] [] [] [] [] [] []) time
        (outputFile (outputWord anchor leaders vista)) := by
  let nodes := vista.nodes.toList
  let suffix := Encoding.natural.encode vista.bottom
  let table := Encoding.sequence Encoding.node nodes++suffix
  let rows := producedRows nodes anchor (anchor-1) leaders
  let width := (AnchorCoefficient.selectedNodes nodes anchor).length
  obtain ⟨inputTime,inputBound,a⟩ := initialize_executes anchor leaders vista
  obtain ⟨buildTime,buildBound,b⟩ := buildRows_executes nodes anchor (anchor-1) leaders suffix
  simp only [nodes,Array.length_toList] at b
  have c := emitInput_executes (Encoding.rationalMatrix.encode rows) (List.replicate width true)
    anchor.bits table (anchor-1).bits (List.replicate vista.nodes.size true) leaders.bits
  have result : Encoding.frame (List.replicate width true)++Encoding.rationalMatrix.encode rows=
      outputWord anchor leaders vista := (outputWord_eq anchor leaders vista).symm
  rw [result] at c
  have composed := a.sequence (b.sequence c)
  refine ⟨_,?_,composed⟩
  let length := (inputWord anchor leaders vista).length
  have codeLength : length=2*anchor.size+1+(2*leaders.size+1)+
      (2*vista.nodes.size.size+1)+table.length := by
    simp only [length,inputWord,Encoding.vista,Encoding.transport,Encoding.product,Encoding.list,
      List.length_append,Encoding.natural_length,Array.length_toList]
    dsimp only [table,nodes,suffix]
    simp only [List.length_append,Encoding.natural_length]
    omega
  have predecessorSize : (anchor-1).size ≤ anchor.size := Nat.size_le_size (Nat.sub_le _ _)
  have nodeBound : nodes.length ≤ table.length := by
    have bound:=AnchorRow.nodes_length nodes
    simp only [table,List.length_append];omega
  have widthBound : width ≤ nodes.length := by
    simpa only [width,AnchorCoefficient.selectedNodes] using List.length_filter_le (fun node=>node.level==anchor) nodes
  have tableBound : (Encoding.sequence Encoding.node nodes).length ≤ table.length := by
    simp only [table,List.length_append];omega
  have matrixBound := matrix_length nodes anchor (anchor-1) leaders table.length tableBound
  have inputCodeBound : table.length+leaders.size+1 ≤ length+1 := by omega
  have matrixRaised := matrixBound.trans (Nat.mul_le_mul_left 10004 (Nat.pow_le_pow_left inputCodeBound 3))
  have outputLength : (outputWord anchor leaders vista).length ≤ 10007*(length+1)^3 := by
    rw [outputWord_eq]
    change (Encoding.frame (List.replicate width true)++Encoding.rationalMatrix.encode rows).length ≤ _
    rw [List.length_append,Encoding.frame_length,List.length_replicate]
    have linear : length+1 ≤ (length+1)^3 := Nat.le_self_pow (by decide) _
    change (Encoding.rationalMatrix.encode rows).length ≤ 10004*(length+1)^3 at matrixRaised
    omega
  have buildPolynomial := buildBudget_polynomial nodes anchor (anchor-1) leaders table.length suffix (by rfl)
  have sizeBound : table.length+anchor.size+(anchor-1).size+leaders.size+1 ≤ 2*(length+1) := by omega
  have buildRaised := buildBound.trans (buildPolynomial.trans
    (Nat.mul_le_mul_left 100000000 (Nat.pow_le_pow_left sizeBound 6)))
  have buildFinal : buildTime ≤ 6400000000*(length+1)^6 := by nlinarith only [buildRaised]
  have cubic : (length+1)^3 ≤ (length+1)^6 := Nat.pow_le_pow_right (by omega) (by decide)
  have linear : length+1 ≤ (length+1)^6 := Nat.le_self_pow (by decide) _
  have positive : 1 ≤ (length+1)^6 := Nat.one_le_pow' _ _
  simp only [Encoding.bits_length,List.length_replicate]
  change inputTime ≤ 2000*(length+1)^3 at inputBound
  change _ ≤ 7000000000*(length+1)^6
  simp only [nodes,Array.length_toList] at nodeBound widthBound
  omega

theorem complete_halts (anchor leaders : Nat) (vista : Executable.Vista) :
    ∃ steps output,
      steps ≤ 7000000000*((inputWord anchor leaders vista).length+1)^6 ∧
      HaltsAt complete.program (inputWord anchor leaders vista) steps output ∧
      output.store 1=outputWord anchor leaders vista := by
  obtain ⟨steps,bounded,last,ran,halted,stored⟩ := complete_executes anchor leaders vista
  refine ⟨steps,last,bounded,⟨?_,halted⟩,?_⟩
  · have start : initial complete.program (inputWord anchor leaders vista)=
        ⟨0,inputFile (inputWord anchor leaders vista) [] [] [] [] [] [] []⟩ := by
      apply congrArg (Config.mk _)
      funext r;fin_cases r <;> simp [inputFile]
    rw [start]
    exact ran
  · rw [stored]
    simp [outputFile]

end Counting.StackMachine.AnchorMatrix
