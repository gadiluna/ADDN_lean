import Counting.StackProtocolVistaComplete

namespace Counting.Machine
open StackMachine.ProtocolVista

def protocolVistaProgram : Program := StackMachine.Compiler.compile complete.program

/-- Fixed physical machine for the actual vista summary used by local
scheduling: bottom round and the all-leader level-zero test. -/
theorem protocolVista_clean (vista : Executable.Vista) (valid : vista.valid=true) :
    ∃ time output,time≤ (20*3000055^2)*((Encoding.vista.encode vista).length+1)^10 ∧
      HaltsAt protocolVistaProgram (Encoding.vista.encode vista) time output ∧
      output.tape.denotes=Turing.Tape.mk₁ ((outputWord vista).map bitSymbol) := by
  obtain ⟨steps,bound,finish,ran,halted,stored⟩:=complete_executes vista valid
  have stackHalt : StackMachine.HaltsAt complete.program (Encoding.vista.encode vista) steps finish := ⟨ran,halted⟩
  obtain ⟨time,output,timeBound,executed,tape⟩:=StackMachine.Compiler.compile_halts stackHalt
  refine ⟨time,output,timeBound.trans ?_,executed,?_⟩
  · let size:=(Encoding.vista.encode vista).length+1
    have positive:1≤ size := by dsimp only [size];omega
    have linear:size≤ size^5:=Nat.le_self_pow (by decide) _
    have one:1≤ size^5:=Nat.one_le_pow _ _ positive
    have base:(Encoding.vista.encode vista).length+50+steps+4≤ 3000055*size^5 := by
      dsimp only [size] at linear one ⊢
      omega
    calc
      _≤ 20*(3000055*size^5)^2:=Nat.mul_le_mul_left 20 (Nat.pow_le_pow_left base 2)
      _= _:=by rw [mul_pow,←pow_mul];simp only [Nat.mul_assoc,size]
  · have value:finish.store 1=outputWord vista := by rw [stored];rfl
    rw [value] at tape
    exact tape

end Counting.Machine
