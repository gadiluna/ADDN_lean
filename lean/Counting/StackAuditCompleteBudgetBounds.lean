import Counting.StackAuditCompleteMajorants

namespace Counting.StackMachine.AuditComplete
set_option maxHeartbeats 1200000

theorem descendantBudget_bounded (vista : Executable.Vista) (weights : Array Nat) (anchor last size : Nat)
    (positive:1≤ size) (anchorBits:anchor.size≤ size) (lastBits:last.size≤ size)
    (vistaBits:(Encoding.vista.encode vista).length≤ size)
    (weightBits:((Encoding.array Encoding.natural).encode weights).length≤ weightsOutputBound size) :
    descendantBudget vista weights anchor last≤ descendantCostBound size := by
  have input:(AuditDescendant.completeInputWord vista weights anchor last).length+1≤ descendantInputBound size := by
    rw [AuditDescendant.completeInputWord_length]
    dsimp only [descendantInputBound]
    omega
  have setup:=Nat.mul_le_mul_left 40 input
  have body:=Nat.mul_le_mul_left AuditDescendant.completeCoefficient (Nat.pow_le_pow_left input 7)
  have output:=Nat.mul_le_mul_left 41 (show anchor.size+((Encoding.array Encoding.natural).encode weights).length+1≤
      size+weightsOutputBound size+1 by omega)
  dsimp only [descendantBudget,descendantCostBound]
  omega

theorem weightsBudget_bounded (vista : Executable.Vista) (weights : Option (Array Nat)) (anchor last size : Nat)
    (positive:1≤ size) (anchorBits:anchor.size≤ size) (lastBits:last.size≤ size)
    (vistaBits:(Encoding.vista.encode vista).length≤ size)
    (weightBits:(optionalWeightsWord weights).length≤ weightsOutputBound size) :
    weightsBudget vista anchor last weights≤ descendantCostBound size+2 := by
  cases weights with
  | none=>simp [weightsBudget]
  | some weights=>
    have bounded:=descendantBudget_bounded vista weights anchor last size positive anchorBits lastBits vistaBits weightBits
    dsimp only [weightsBudget]
    omega

/-- Output lengths used in the next phase are bounded from the actual
executions of the concrete Gaussian and post-solver programs. -/
theorem selectedBudget_bounded (vista : Executable.Vista) (leaders candidate last anchor size : Nat)
    (positive:1≤ size) (leaderBits:leaders.size≤ size) (candidateBits:candidate.size≤ size)
    (lastBits:last.size≤ size) (anchorBits:anchor.size≤ size)
    (vistaBits:(Encoding.vista.encode vista).length≤ size)
    (anchorBound:anchor≤ vista.nodes.size) (valid:vista.valid=true) :
    selectedBudget vista leaders candidate last anchor≤ selectedCostBound size := by
  let values:=solvedValues vista leaders anchor
  have matrix:(AnchorMatrix.inputWord anchor leaders vista).length+1≤ anchorInputBound size := by
    simp only [AnchorMatrix.inputWord,List.length_append,Encoding.natural_length]
    dsimp only [anchorInputBound]
    omega
  have solverCost:=Nat.mul_le_mul_left AnchorSolve.polynomialCoefficient (Nat.pow_le_pow_left matrix 4500)
  have solverLength: (AuditPositive.inputWord values).length≤ solverOutputBound size := by
    have actual:=solvedValues_length vista leaders anchor
    change (AuditPositive.inputWord values).length≤ _ at actual
    dsimp only [solverOutputBound]
    omega
  have postInput:(AuditPostSolver.inputWord vista candidate anchor values).length+1≤ postInputBound size := by
    simp only [AuditPostSolver.inputWord,List.length_append,Encoding.natural_length,Encoding.frame_length]
    dsimp only [postInputBound]
    omega
  have postCost:=Nat.mul_le_mul_left AuditPostSolver.completeCoefficient (Nat.pow_le_pow_left postInput 51)
  have postLength:(AuditPostSolver.outputWord vista candidate anchor values).length≤ weightsOutputBound size := by
    have actual:=postSolver_output_length vista candidate anchor values anchorBound valid
    dsimp only [weightsOutputBound]
    omega
  have weightsLength:(optionalWeightsWord (AuditPostSolver.result vista candidate anchor values)).length≤ weightsOutputBound size := by
    have relation:(optionalWeightsWord (AuditPostSolver.result vista candidate anchor values)).length≤
        (AuditPostSolver.outputWord vista candidate anchor values).length := by
      cases answer:AuditPostSolver.result vista candidate anchor values <;>
        simp [optionalWeightsWord,AuditPostSolver.outputWord,answer,Encoding.optional]
    exact relation.trans postLength
  have weightCost:=weightsBudget_bounded vista (AuditPostSolver.result vista candidate anchor values) anchor last size
    positive anchorBits lastBits vistaBits weightsLength
  have suffix:suffixBudget vista candidate last anchor values≤ suffixCostBound size := by
    have setup:=Nat.mul_le_mul_left 30 postInput
    dsimp only [suffixBudget,suffixCostBound]
    omega
  have setup:=Nat.mul_le_mul_left 30 matrix
  dsimp only [selectedBudget,selectedCostBound]
  change suffixBudget vista candidate last anchor (solvedValues vista leaders anchor)≤ suffixCostBound size at suffix
  omega

theorem afterPrefixBudget_bounded (vista : Executable.Vista) (leaders candidate last : Nat) :
    afterPrefixBudget vista leaders candidate last (Executable.auditPrefix? vista leaders candidate last)≤
      afterPrefixCostBound ((AuditPrefix.inputWord vista leaders candidate last).length+1) := by
  let size:=(AuditPrefix.inputWord vista leaders candidate last).length+1
  have positive:1≤ size := by dsimp only [size];omega
  have inputSize:=AuditPrefix.inputWord_length vista leaders candidate last
  have leaderBits:leaders.size≤ size := by dsimp only [size];omega
  have candidateBits:candidate.size≤ size := by dsimp only [size];omega
  have lastBits:last.size≤ size := by dsimp only [size];omega
  have vistaBits:(Encoding.vista.encode vista).length≤ size := by dsimp only [size];omega
  cases found:Executable.auditPrefix? vista leaders candidate last with
  | none=>
    change 27≤ afterPrefixCostBound size
    dsimp only [afterPrefixCostBound]
    omega
  | some anchor=>
    obtain ⟨valid,anchorLast,lastNodes⟩:=prefix_success_bounds vista leaders candidate last anchor found
    have nodeCount:=Encoding.array_size_le_length Encoding.node vista.nodes
      (by intro node _;exact Encoding.node_positive_length node)
    have nodeCode:((Encoding.array Encoding.node).encode vista.nodes).length≤ (Encoding.vista.encode vista).length := by
      change _≤ (((Encoding.array Encoding.node).encode vista.nodes)++Encoding.natural.encode vista.bottom).length
      simp only [List.length_append];omega
    have anchorSmall:anchor+1≤ size := by omega
    have anchorBits:anchor.size≤ size := (Nat.size_le.mpr Nat.lt_two_pow_self).trans (by omega)
    have codeBits:(anchor+1).size≤ size := (Nat.size_le.mpr Nat.lt_two_pow_self).trans anchorSmall
    have body:=selectedBudget_bounded vista leaders candidate last anchor size positive leaderBits candidateBits
      lastBits anchorBits vistaBits (by omega) valid
    dsimp only [afterPrefixBudget,AuditPrefix.anchorCode,dispatchBudget,afterPrefixCostBound]
    change 20*((anchor+1).size+1)+(100*((anchor+1).size+anchor.size+1)+
      selectedBudget vista leaders candidate last anchor+2)+5≤ 20*(size+1)+100*(size+size+1)+selectedCostBound size+9
    omega

theorem rawBudget_bounded (vista : Executable.Vista) (leaders candidate last : Nat) :
    rawBudget vista leaders candidate last≤ rawCostBound ((AuditPrefix.inputWord vista leaders candidate last).length+1) := by
  have after:=afterPrefixBudget_bounded vista leaders candidate last
  dsimp only [rawBudget,rawCostBound]
  omega

theorem completeBudget_bounded (vista : Executable.Vista) (leaders candidate last : Nat) :
    completeBudget vista leaders candidate last≤ completeCostBound ((AuditPrefix.inputWord vista leaders candidate last).length+1) := by
  have raw:=rawBudget_bounded vista leaders candidate last
  dsimp only [completeBudget,completeCostBound]
  omega

end Counting.StackMachine.AuditComplete
