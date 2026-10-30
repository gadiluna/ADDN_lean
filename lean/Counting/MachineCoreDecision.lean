import Counting.StackCoreDecisionPolynomial

namespace Counting.Machine
open StackMachine.CoreDecision StackMachine.ProtocolDecision

def coreDecisionProgram : Program := StackMachine.Compiler.compile complete.program

/-- One fixed physical finite-alphabet machine executes the full original
scheduledPlan from leader count and the local serialized vista. Its bound is
uniform; every arithmetic, scanning, branching, solving and cleanup step is
charged. Graph validity is the established invariant of physical vistas. -/
theorem coreDecision_polynomial : ∃ coefficient degree,
    ∀ (vista : Executable.Vista) (leaders : Nat),vista.valid=true → 0<leaders →
      ∃ time output,
        time≤ coefficient*((inputWord vista leaders).length+1)^degree ∧
        HaltsAt coreDecisionProgram (inputWord vista leaders) time output ∧
        output.tape.denotes=Turing.Tape.mk₁
          ((outputWord (Executable.coreScheduledPlan leaders vista).eval).map bitSymbol) := by
  obtain ⟨coefficient,degree,polynomial⟩:=complete_polynomial
  refine ⟨20*(coefficient+83)^2,(degree+1)*2,?_⟩
  intro vista leaders valid positive
  obtain ⟨steps,bound,finish,ran,halted,stored⟩:=polynomial vista leaders valid positive
  have stackHalt : StackMachine.HaltsAt complete.program (inputWord vista leaders) steps finish := ⟨ran,halted⟩
  obtain ⟨time,output,timeBound,executed,tape⟩:=StackMachine.Compiler.compile_halts stackHalt
  refine ⟨time,output,timeBound.trans ?_,executed,?_⟩
  · let size:=(inputWord vista leaders).length+1
    have positive:1≤ size := by dsimp only [size];omega
    have linear:size≤ size^(degree+1):=Nat.le_self_pow (by omega) _
    have one:1≤ size^(degree+1):=Nat.one_le_pow _ _ positive
    have raised:=bound.trans (Nat.mul_le_mul_left coefficient
      (Nat.pow_le_pow_right positive (show degree≤ degree+1 by omega)))
    have base:(inputWord vista leaders).length+78+steps+4≤ (coefficient+83)*size^(degree+1) := by
      rw [Nat.add_mul]
      dsimp only [size] at linear one raised ⊢
      omega
    calc
      _≤ 20*((coefficient+83)*size^(degree+1))^2:=Nat.mul_le_mul_left 20 (Nat.pow_le_pow_left base 2)
      _= _:=by rw [mul_pow,←pow_mul];simp only [Nat.mul_assoc,size]
  · have value:finish.store 1=outputWord (Executable.coreScheduledPlan leaders vista).eval := by rw [stored];rfl
    rw [value] at tape
    exact tape

end Counting.Machine
