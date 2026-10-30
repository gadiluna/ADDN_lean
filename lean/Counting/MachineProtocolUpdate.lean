import Counting.StackProtocolUpdateComplete
import Counting.StackCompilerComplete

namespace Counting.Machine
open StackMachine.ProtocolUpdate
set_option maxRecDepth 10000
set_option exponentiation.threshold 1024

def protocolUpdateProgram : Program := StackMachine.Compiler.compile complete.program
def protocolUpdateCoefficient : Nat := 20*(completeCoefficient+163)^2

/-- The finite-tape machine implements the exact optional vista update
on every local input admitted by the distributed execution model. -/
theorem protocolUpdate_clean (old : Executable.Vista)
    (messages : List (Executable.Vista×Nat)) (degree : Nat) (valid : old.valid=true)
    (received : ∀m∈messages,m.1.valid=true ∧ 0 < m.2 ∧
      (m.1.node m.1.bottom).level=(old.node old.bottom).level) :
    ∃time output,time≤protocolUpdateCoefficient*((inputWord old messages degree).length+1)^544 ∧
      HaltsAt protocolUpdateProgram (inputWord old messages degree) time output ∧
      output.tape.denotes=Turing.Tape.mk₁
        ((outputWord (Executable.updateVista? old messages degree)).map bitSymbol) := by
  obtain ⟨steps,bounded,last,ran,halted,stored⟩:=complete_executes old messages degree valid received
  have stackHalt:StackMachine.HaltsAt complete.program (inputWord old messages degree) steps last:=⟨ran,halted⟩
  obtain ⟨time,output,timeBound,execution,tape⟩:=StackMachine.Compiler.compile_halts stackHalt
  refine ⟨time,output,timeBound.trans ?_,execution,?_⟩
  · let N:=(inputWord old messages degree).length
    have linear:N+1≤(N+1)^272:=Nat.le_self_pow (by decide) _
    have positive:1≤(N+1)^272:=Nat.one_le_pow' _ _
    have base:N+158+steps+4≤(completeCoefficient+163)*(N+1)^272 := by
      change steps≤completeCoefficient*(N+1)^272 at bounded
      rw [Nat.add_mul]
      omega
    calc
      _≤20*((completeCoefficient+163)*(N+1)^272)^2:=
        Nat.mul_le_mul_left 20 (Nat.pow_le_pow_left base 2)
      _=20*((completeCoefficient+163)^2*(N+1)^544):=by
        rw [Nat.mul_pow,←Nat.pow_mul]
      _=protocolUpdateCoefficient*(N+1)^544:=
        (Nat.mul_assoc 20 ((completeCoefficient+163)^2) ((N+1)^544)).symm
  · rw [stored] at tape
    exact tape

end Counting.Machine
