import Counting.StackVistaMessagesPolynomial
import Counting.StackCompilerComplete

namespace Counting.Machine
open StackMachine.DagUpdate.Receive

def vistaMessagesProgram : Program := StackMachine.Compiler.compile completeMessages.program

/-- The complete received-message fold runs on a finite-alphabet tape
machine in polynomial time, including input parsing and complete output
tape cleanup. Each repeated message is represented by one binary count. -/
theorem vistaMessages_clean (state : Executable.MergeState)
    (messages : List (Executable.Vista×Nat)) :
    ∃ time output,
      time≤20*(completeMessagesCoefficient+99)^2*((messagesInput state messages).length+1)^122 ∧
      HaltsAt vistaMessagesProgram (messagesInput state messages) time output ∧
      output.tape.denotes=Turing.Tape.mk₁ ((messagesOutput state messages).map bitSymbol) := by
  obtain ⟨steps,last,bounded,halted,stored⟩ := completeMessages_halts state messages
  obtain ⟨time,output,timeBound,executed,tape⟩ := StackMachine.Compiler.compile_halts halted
  refine ⟨time,output,timeBound.trans ?_,executed,?_⟩
  · let size := (messagesInput state messages).length
    have linear : size+1≤(size+1)^61 := Nat.le_self_pow (by decide) _
    have positive : 1≤(size+1)^61 := Nat.one_le_pow' 61 size
    have base : size+94+steps+4≤(completeMessagesCoefficient+99)*(size+1)^61 := by
      change steps≤completeMessagesCoefficient*(size+1)^61 at bounded
      simp only [Nat.add_mul]
      omega
    calc
      _ ≤ 20*((completeMessagesCoefficient+99)*(size+1)^61)^2 :=
        Nat.mul_le_mul_left 20 (Nat.pow_le_pow_left base 2)
      _ = _ := by ring
  · rw [stored] at tape
    exact tape

end Counting.Machine
