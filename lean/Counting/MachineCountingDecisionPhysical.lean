import Counting.MachineProtocolDecision
import Counting.MachineCoreDecision
import Counting.CountingSizeEncoding

namespace Counting.Machine
open Executable

private theorem decisionInput_physical_bound {V : Type} [Fintype V]
    (G : Nat → V → V → Nat) (leader : V → Bool) (t : Nat) (observer : V) (vista : Vista)
    (valid : vista.valid=true) (depth : (vista.node vista.bottom).level=t)
    (physical : decodeNode vista t vista.bottom=Counting.history G leader t observer)
    (leaders M : Nat) (mass : ∀ r,0<r → r≤ t → arcMass G r≤ M) :
    let n:=Fintype.card V
    let K:=(t+1)*n
    let B:=t+K+M.size+n+1
    (StackMachine.ProtocolDecision.inputWord vista leaders).length+1≤
      K*(8*B+9+n*(4*B+2))+2*leaders.size+4 := by
  dsimp only
  have code:=Encoding.physical_vista_encoding_length G leader t observer vista valid depth physical M mass
  dsimp only at code
  simp only [StackMachine.ProtocolDecision.inputWord,List.length_append,Encoding.natural_length]
  omega

/-- Physical-population size bound for the optimized decision machine.
Constants are fixed before the population, graph, and binary labels. -/
theorem scheduledDecision_physical_polynomial : ∃ coefficient degree,
    ∀ {V : Type} [Fintype V] (G : Nat → V → V → Nat) (leader : V → Bool)
      (t : Nat) (observer : V) (vista : Vista)
      (_ : vista.valid=true) (_ : (vista.node vista.bottom).level=t)
      (_ : decodeNode vista t vista.bottom=Counting.history G leader t observer)
      (leaders M : Nat) (_ : ∀ r,0<r → r≤ t → arcMass G r≤ M),
      let n:=Fintype.card V
      let K:=(t+1)*n
      let B:=t+K+M.size+n+1
      ∃ time output,
        time≤ coefficient*(K*(8*B+9+n*(4*B+2))+2*leaders.size+4)^degree ∧
        HaltsAt scheduledDecisionProgram (StackMachine.ProtocolDecision.inputWord vista leaders) time output ∧
        output.tape.denotes=Turing.Tape.mk₁
          ((StackMachine.ProtocolDecision.outputWord (scheduledPlan leaders vista).eval).map bitSymbol) := by
  obtain ⟨coefficient,degree,run⟩:=scheduledDecision_polynomial
  refine ⟨coefficient,degree,?_⟩
  intro V inst G leader t observer vista valid depth physical leaders M mass
  dsimp only
  obtain ⟨time,output,bound,halted,tape⟩:=run vista leaders valid
  have size:=decisionInput_physical_bound G leader t observer vista valid depth physical leaders M mass
  exact ⟨time,output,bound.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left size degree)),halted,tape⟩

/-- The same population-and-label polynomial applies to the concrete core
schedule, including its own odd-round guard and complete audit. -/
theorem coreDecision_physical_polynomial : ∃ coefficient degree,
    ∀ {V : Type} [Fintype V] (G : Nat → V → V → Nat) (leader : V → Bool)
      (t : Nat) (observer : V) (vista : Vista)
      (_ : vista.valid=true) (_ : (vista.node vista.bottom).level=t)
      (_ : decodeNode vista t vista.bottom=Counting.history G leader t observer)
      (leaders M : Nat) (_ : 0<leaders) (_ : ∀ r,0<r → r≤ t → arcMass G r≤ M),
      let n:=Fintype.card V
      let K:=(t+1)*n
      let B:=t+K+M.size+n+1
      ∃ time output,
        time≤ coefficient*(K*(8*B+9+n*(4*B+2))+2*leaders.size+4)^degree ∧
        HaltsAt coreDecisionProgram (StackMachine.ProtocolDecision.inputWord vista leaders) time output ∧
        output.tape.denotes=Turing.Tape.mk₁
          ((StackMachine.ProtocolDecision.outputWord (coreScheduledPlan leaders vista).eval).map bitSymbol) := by
  obtain ⟨coefficient,degree,run⟩:=coreDecision_polynomial
  refine ⟨coefficient,degree,?_⟩
  intro V inst G leader t observer vista valid depth physical leaders M positive mass
  dsimp only
  obtain ⟨time,output,bound,halted,tape⟩:=run vista leaders valid positive
  have size:=decisionInput_physical_bound G leader t observer vista valid depth physical leaders M mass
  exact ⟨time,output,bound.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left size degree)),halted,tape⟩

end Counting.Machine
