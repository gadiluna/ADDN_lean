import Counting.StackVistaRawPolynomial
import Counting.StackCompilerComplete

namespace Counting.Machine
open StackMachine.DagUpdate.Raw

def rawVistaProgram : Program := StackMachine.Compiler.compile complete.program

def rawVistaCoefficient : Nat := 20*(completeCoefficient+99)^2

/-- The actual finite tape machine implements a receiver update in a
uniform polynomial number of transitions and erases its entire work tape. -/
theorem rawVista_clean (round : Nat) (leader : Bool) (degree : Nat) (old : Executable.Vista)
    (messages : List (Executable.Vista×Nat)) :
    ∃ time output,
      time ≤ rawVistaCoefficient*((inputWord round leader degree old messages).length+1)^122 ∧
      HaltsAt rawVistaProgram (inputWord round leader degree old messages) time output ∧
      output.tape.denotes = Turing.Tape.mk₁
        ((Encoding.vista.encode (updated round leader degree old messages)).map bitSymbol) := by
  obtain ⟨steps,bounded,last,ran,halted,stored⟩ := complete_polynomial round leader degree old messages
  have stackHalt : StackMachine.HaltsAt complete.program
      (inputWord round leader degree old messages) steps last := ⟨ran,halted⟩
  obtain ⟨time,output,timeBound,execution,tape⟩ := StackMachine.Compiler.compile_halts stackHalt
  refine ⟨time,output,timeBound.trans ?_,execution,?_⟩
  · let N := (inputWord round leader degree old messages).length
    have linear : N+1 ≤ (N+1)^61 := Nat.le_self_pow (by decide) _
    have positive : 1 ≤ (N+1)^61 := Nat.one_le_pow' 61 N
    have base : N+94+steps+4 ≤ (completeCoefficient+99)*(N+1)^61 := by
      change steps ≤ completeCoefficient*(N+1)^61 at bounded
      rw [Nat.add_mul]
      omega
    calc
      _ ≤ 20*((completeCoefficient+99)*(N+1)^61)^2 :=
        Nat.mul_le_mul_left 20 (Nat.pow_le_pow_left base 2)
      _ = _ := by dsimp [N,rawVistaCoefficient]; ring
  · rw [stored] at tape
    exact tape

/-- On the physical model's common-round inputs, the same machine computes
the exact valid raw update, not merely an isomorphic proxy. -/
theorem rawVista_physical (round : Nat) (leader : Bool) (degree : Nat) (old : Executable.Vista)
    (messages : List (Executable.Vista×Nat)) (valid : old.valid = true)
    (roundEq : (old.node old.bottom).level = round) (leaderEq : (old.node old.bottom).leader = leader)
    (messageValid : ∀ message ∈ messages, message.1.valid = true ∧
      (message.1.node message.1.bottom).level = round) :
    ∃ time output,
      time ≤ rawVistaCoefficient*((inputWord round leader degree old messages).length+1)^122 ∧
      HaltsAt rawVistaProgram (inputWord round leader degree old messages) time output ∧
      output.tape.denotes = Turing.Tape.mk₁
        ((Encoding.vista.encode (Executable.rawUpdate old messages degree)).map bitSymbol) := by
  simpa only [updated_eq_rawUpdate round leader degree old messages valid roundEq leaderEq messageValid]
    using rawVista_clean round leader degree old messages

end Counting.Machine
