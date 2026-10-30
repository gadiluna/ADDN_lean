import Counting.StackAuditDescendantComplete

namespace Counting.Machine
open StackMachine.AuditDescendant

def auditDescendantProgram : Program := StackMachine.Compiler.compile complete.program

/-- Complete finite-alphabet machine for the literal descendant inequalities.
All loop counters are read from its binary input; the exact round bound is
the one already established by the full audit's prefix guard. -/
theorem auditDescendant_clean (vista : Executable.Vista) (weights : Array Nat) (anchor last : Nat)
    (fits : last≤vista.nodes.size) :
    ∃ time output,
      time≤(20*(completeCoefficient+51)^2)*((completeInputWord vista weights anchor last).length+1)^14 ∧
      HaltsAt auditDescendantProgram (completeInputWord vista weights anchor last) time output ∧
      output.tape.denotes=Turing.Tape.mk₁ ([Executable.auditDescendants vista weights anchor last].map bitSymbol) := by
  obtain ⟨steps,finish,bound,halted,stored⟩:=complete_halts vista weights anchor last fits
  obtain ⟨time,output,timeBound,executed,tape⟩:=StackMachine.Compiler.compile_halts halted
  refine ⟨time,output,timeBound.trans ?_,executed,?_⟩
  · let size:=(completeInputWord vista weights anchor last).length
    have linear : size+1≤(size+1)^7:=Nat.le_self_pow (by decide) _
    have positive : 1≤(size+1)^7:=Nat.one_le_pow' 7 size
    have base : size+46+steps+4≤(completeCoefficient+51)*(size+1)^7 := by
      change steps≤completeCoefficient*(size+1)^7 at bound
      simp only [Nat.add_mul]
      omega
    calc
      _≤20*((completeCoefficient+51)*(size+1)^7)^2:=
        Nat.mul_le_mul_left 20 (Nat.pow_le_pow_left base 2)
      _=_:=by ring
  · rw [stored] at tape
    exact tape

end Counting.Machine
