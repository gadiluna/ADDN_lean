import Counting.StackProtocolAdvanceComplete

namespace Counting.StackMachine.ProtocolAdvance
open Routine Executable
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
set_option exponentiation.threshold 1024

theorem decisionBudget_polynomial (core : Bool) : ∃C d,∀(vista : Vista) (leaders : Nat),vista.valid=true →
    decisionBudget core leaders vista≤C*((ProtocolDecision.inputWord vista leaders).length+1)^d := by
  cases core with
  | false=>simpa only [decisionBudget,Bool.false_eq_true,if_false] using ProtocolDecision.completeBudget_polynomial
  | true=>simpa only [decisionBudget,if_true] using CoreDecision.completeBudget_polynomial

theorem decideBudget_polynomial (core : Bool) : ∃C d,∀(vista : Vista) (leaders : Nat),vista.valid=true →
    decideBudget core leaders vista≤C*((ProtocolDecision.inputWord vista leaders).length+1)^d := by
  obtain ⟨C,d,polynomial⟩:=decisionBudget_polynomial core
  refine ⟨71*C+202,d+1,?_⟩
  intro vista leaders valid
  let N:=(ProtocolDecision.inputWord vista leaders).length+1
  have linear:N≤N^(d+1):=Nat.le_self_pow (by omega) _
  have one:1≤N^(d+1):=Nat.one_le_pow' _ _
  have raised:(decisionBudget core leaders vista)≤C*N^(d+1):=
    (polynomial vista leaders valid).trans (Nat.mul_le_mul_left C
      (Nat.pow_le_pow_right (by omega) (by omega)))
  unfold decideBudget
  change 200*N+71*decisionBudget core leaders vista+2≤(71*C+202)*N^(d+1)
  rw [Nat.add_mul,Nat.mul_assoc]
  omega

theorem input_component_bounds (state : LocalState) (messages : List (Vista×Nat)) (degree : Nat) :
    (stateWord state).length+1≤(inputWord state messages degree).length+1 ∧
    (ProtocolUpdate.inputWord state.vista messages degree).length+1≤(inputWord state messages degree).length+1 ∧
    state.leaders.size≤(inputWord state messages degree).length+1 := by
  rw [stateWord_fields,inputWord_fields,ProtocolUpdate.inputWord_eq]
  simp only [List.length_append,Encoding.frame_length,Encoding.natural_length]
  change _ ∧ 2*(Encoding.vista.encode state.vista).length+1+
    (2*(messagesCodec.encode messages).length+1)+(2*degree.size+1)+1≤ _ ∧ _
  omega

private theorem completeBudget_polynomial_with_coefficient (core : Bool) (U : Nat)
    (coefficient_eq : ProtocolUpdate.completeCoefficient = U) : ∃C d,
    ∀(state : LocalState) (messages : List (Vista×Nat)) (degree : Nat) (updated : Vista),
      state.vista.valid=true →
      (∀m∈messages,m.1.valid=true ∧ 0 < m.2 ∧ (m.1.node m.1.bottom).level=(state.vista.node state.vista.bottom).level) →
      updateVista? state.vista messages degree=some updated →
      completeBudget core state messages degree updated≤C*((inputWord state messages degree).length+1)^d := by
  obtain ⟨D,d,decisionPoly⟩:=decideBudget_polynomial core
  let C:=D*(U+5)^d+13*U+200
  refine ⟨257*(C+4),272*(d+1),?_⟩
  intro state messages degree updated valid received success
  let N:=(inputWord state messages degree).length+1
  let P:=N^(272*(d+1))
  have positive:1≤N:=by clear coefficient_eq;dsimp [N];omega
  obtain ⟨stateBound,updateInput,leadersBound⟩:=input_component_bounds state messages degree
  change (stateWord state).length+1≤N at stateBound
  change (ProtocolUpdate.inputWord state.vista messages degree).length+1≤N at updateInput
  change state.leaders.size≤N at leadersBound
  have linear:N≤P:=Nat.le_self_pow (by clear coefficient_eq;omega) _
  have one:1≤P:=one_le_pow₀ positive
  have powRaised:N^272≤P:=Nat.pow_le_pow_right positive (by clear coefficient_eq;omega)
  obtain ⟨time,bounded,run⟩:=ProtocolUpdate.complete_executes state.vista messages degree valid received
  rw [coefficient_eq] at bounded
  have outputBound:=ProtocolUpdate.output_length_of_execution ProtocolUpdate.complete
    (ProtocolUpdate.inputWord state.vista messages degree)
    (ProtocolUpdate.outputWord (updateVista? state.vista messages degree)) time run
  rw [success] at outputBound
  change (Encoding.vista.encode updated).length+1≤(ProtocolUpdate.inputWord state.vista messages degree).length+time at outputBound
  have updateCost:updateBudget state.vista messages degree≤U*N^272:=by
    unfold updateBudget
    rw [coefficient_eq]
    exact Nat.mul_le_mul_left U (Nat.pow_le_pow_left updateInput 272)
  clear coefficient_eq
  have updaterBound:time≤U*N^272:=bounded.trans
    (Nat.mul_le_mul_left U (Nat.pow_le_pow_left updateInput 272))
  have initialLinear:N≤N^272:=Nat.le_self_pow (by decide) _
  have viewBound:(Encoding.vista.encode updated).length≤(U+1)*N^272 := by
    rw [Nat.add_mul,Nat.one_mul]
    omega
  have decisionInput:(ProtocolDecision.inputWord updated state.leaders).length+1≤(U+5)*N^272 := by
    simp only [ProtocolDecision.inputWord,List.length_append,Encoding.natural_length]
    rw [show U+5=(U+1)+4 by omega,Nat.add_mul]
    omega
  have decisionBound:decideBudget core state.leaders updated≤D*(U+5)^d*P := by
    calc
      _≤D*((ProtocolDecision.inputWord updated state.leaders).length+1)^d:=decisionPoly _ _ (updateVista_valid _ _ _ _ success)
      _≤D*((U+5)*N^272)^d:=Nat.mul_le_mul_left D (Nat.pow_le_pow_left decisionInput d)
      _=D*(U+5)^d*N^(272*d):=by rw [Nat.mul_pow,←Nat.pow_mul,Nat.mul_assoc]
      _≤D*(U+5)^d*P:=Nat.mul_le_mul_left _ (Nat.pow_le_pow_right positive (by omega))
  have updateRaised:updateBudget state.vista messages degree≤U*P:=updateCost.trans (Nat.mul_le_mul_left U powRaised)
  have viewRaised:(Encoding.vista.encode updated).length≤(U+1)*P:=viewBound.trans (Nat.mul_le_mul_left (U+1) powRaised)
  have raw:rawBudget core state messages degree updated≤C*P := by
    unfold rawBudget activeBudget
    change 20*N+60*((stateWord state).length+1)+
      (20*((ProtocolUpdate.inputWord state.vista messages degree).length+1)+
       updateBudget state.vista messages degree+12*(Encoding.vista.encode updated).length+
       decideBudget core state.leaders updated+20)+10≤C*P
    dsimp only [C]
    rw [Nat.add_mul,Nat.add_mul]
    simp only [Nat.mul_assoc] at decisionBound ⊢
    rw [Nat.add_mul,Nat.one_mul] at viewRaised
    omega
  unfold completeBudget
  change 257*(rawBudget core state messages degree updated+(inputWord state messages degree).length+3)≤257*(C+4)*P
  rw [Nat.mul_assoc]
  apply Nat.mul_le_mul_left
  rw [Nat.add_mul]
  omega

theorem completeBudget_polynomial (core : Bool) : ∃C d,
    ∀(state : LocalState) (messages : List (Vista×Nat)) (degree : Nat) (updated : Vista),
      state.vista.valid=true →
      (∀m∈messages,m.1.valid=true ∧ 0 < m.2 ∧ (m.1.node m.1.bottom).level=(state.vista.node state.vista.bottom).level) →
      updateVista? state.vista messages degree=some updated →
      completeBudget core state messages degree updated≤C*((inputWord state messages degree).length+1)^d :=
  completeBudget_polynomial_with_coefficient core ProtocolUpdate.completeCoefficient rfl

/-- Uniform polynomial runtime of the complete concrete transition; all
parameters are local protocol inputs and every work cell is cleaned. -/
theorem complete_polynomial (core : Bool) : ∃C d,
    ∀(state : LocalState) (messages : List (Vista×Nat)) (degree : Nat),
      state.vista.valid=true →
      (∀m∈messages,m.1.valid=true ∧ 0 < m.2 ∧ (m.1.node m.1.bottom).level=(state.vista.node state.vista.bottom).level) →
      ∃time≤C*((inputWord state messages degree).length+1)^d,
        Executes (complete core) (inputStore 254 (inputWord state messages degree)) time
          (outputStore 254 (outputWord (transition core state messages degree))) := by
  obtain ⟨C,d,poly⟩:=completeBudget_polynomial core
  refine ⟨C,d,?_⟩
  intro state messages degree valid received
  obtain ⟨updated,success,_,_⟩:=updateVista_total state.vista messages degree valid received
  obtain ⟨time,bound,run⟩:=complete_executes core state messages degree updated valid received success
  exact ⟨time,bound.trans (poly state messages degree updated valid received success),run⟩

end Counting.StackMachine.ProtocolAdvance
