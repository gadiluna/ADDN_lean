import Counting.StackAuditPostSolverComplete
import Counting.AuditPropagationInputBounds

namespace Counting.StackMachine.AuditPostSolver
set_option maxHeartbeats 1600000

/-- A successful candidate check cannot manufacture a larger natural
payload than the actual serialized solver result. -/
theorem candidate_some_length (values : Option (Array Rat)) (candidate : Nat) (natural : Array Nat)
    (success : AuditCandidate.result values candidate=some natural) :
    ((Encoding.array Encoding.natural).encode natural).length ≤ (AuditPositive.inputWord values).length := by
  have bounded:=AuditPositive.output_length values
  cases converted : AuditPositive.result values with
  | none=>simp [AuditCandidate.result,converted] at success
  | some found=>
    have same : found=natural := by
      simp only [AuditCandidate.result,converted,bind,Option.bind_some] at success
      split at success
      · exact Option.some.inj success
      · contradiction
    rw [←same]
    change ((Encoding.optional (Encoding.array Encoding.natural)).encode (AuditPositive.result values)).length ≤ _ at bounded
    rw [converted] at bounded
    simp only [Encoding.optional,List.length_cons] at bounded
    omega

def successCoefficient : Nat := AuditPropagation.propagationCoefficient+
  AuditBalance.balanceCoefficient*1100^17+1000000

theorem successBudget_polynomial (anchor : Nat) (vista : Executable.Vista) (natural : Array Nat)
    (fits : anchor≤vista.nodes.size) :
    successBudget anchor vista natural ≤
      successCoefficient*((AuditPropagation.propagationInputWord anchor vista natural).length+1)^51 := by
  let S:=(AuditPropagation.propagationInputWord anchor vista natural).length+1
  let weights:=Executable.propagateWeights vista anchor natural
  let oldWord:=(Encoding.array Encoding.natural).encode natural
  let newWord:=(Encoding.array Encoding.natural).encode weights
  have positive : 1 ≤ S := by dsimp only [S];omega
  have inputSize : (AuditPropagation.propagationInputWord anchor vista natural).length=
      2*anchor.size+1+(2*(Encoding.vista.encode vista).length+1)+oldWord.length := by
    simp only [AuditPropagation.propagationInputWord,AuditPropagation.propagationInputCodec,
      Encoding.product,Encoding.framed,List.length_append,Encoding.natural_length,Encoding.frame_length,oldWord]
    omega
  have oldBound : oldWord.length ≤ S := by dsimp only [S];omega
  have codeBound : (Encoding.vista.encode vista).length ≤ S := by dsimp only [S];omega
  have anchorBound : anchor.size ≤ S := by dsimp only [S];omega
  have outputBound:=AuditPropagation.propagateWeights_input_encoded_length anchor vista natural fits
  change newWord.length ≤ 1080*S^3 at outputBound
  have linear : S ≤ S^3 := Nat.le_self_pow (by decide) _
  have one : 1 ≤ S^3 := Nat.one_le_pow _ _ positive
  have balanceSize : (AuditBalance.balanceInputWord anchor vista weights).length+1=
      2*anchor.size+1+(2*(Encoding.vista.encode vista).length+1)+newWord.length+1 := by
    simp only [AuditBalance.balanceInputWord,AuditPropagation.propagationInputWord,
      AuditPropagation.propagationInputCodec,Encoding.product,Encoding.framed,List.length_append,
      Encoding.natural_length,Encoding.frame_length,newWord]
    omega
  have balanceBase : (AuditBalance.balanceInputWord anchor vista weights).length+1 ≤ 1100*S^3 := by omega
  have balance : AuditBalance.balanceCoefficient*((AuditBalance.balanceInputWord anchor vista weights).length+1)^17 ≤
      (AuditBalance.balanceCoefficient*1100^17)*S^51 := by
    calc
      _ ≤ AuditBalance.balanceCoefficient*(1100*S^3)^17 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left balanceBase 17)
      _ = _ := by rw [mul_pow,←pow_mul];simp only [Nat.mul_assoc]
  have propagation := Nat.mul_le_mul_left AuditPropagation.propagationCoefficient
    (Nat.pow_le_pow_right positive (by decide : 32≤51))
  have cubic : S^3 ≤ S^51 := Nat.pow_le_pow_right positive (by decide)
  have rest : 20*(oldWord.length+(Encoding.vista.encode vista).length+anchor.size+2)+
      (5*newWord.length+2)+20*(newWord.length+(Encoding.vista.encode vista).length+anchor.size+2)+
      10*(newWord.length+1)+5 ≤ 1000000*S^51 := by omega
  change successBudget anchor vista natural ≤ successCoefficient*S^51
  dsimp only [successBudget]
  change 20*(oldWord.length+(Encoding.vista.encode vista).length+anchor.size+2)+
    AuditPropagation.propagationCoefficient*S^32+(5*newWord.length+2)+
    20*(newWord.length+(Encoding.vista.encode vista).length+anchor.size+2)+
    AuditBalance.balanceCoefficient*((AuditBalance.balanceInputWord anchor vista weights).length+1)^17+
    10*(newWord.length+1)+5 ≤ successCoefficient*S^51
  dsimp only [successCoefficient]
  simp only [Nat.add_mul]
  omega

end Counting.StackMachine.AuditPostSolver
