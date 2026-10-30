import Counting.StackProtocolAdvancePolynomial

namespace Counting.Machine
open StackMachine.ProtocolAdvance

def advanceProgram (core : Bool) : Program := StackMachine.Compiler.compile (complete core).program

/-- A single fixed physical finite-alphabet program for each protocol
executes its genuine complete local transition. The machine reads only the
serialized local state, incoming compressed messages, and learned outdegree. -/
theorem advance_polynomial (core : Bool) : ∃C d,
    ∀(state : Executable.LocalState) (messages : List (Executable.Vista×Nat)) (degree : Nat),
      state.vista.valid=true →
      (∀m∈messages,m.1.valid=true ∧ 0 < m.2 ∧ (m.1.node m.1.bottom).level=(state.vista.node state.vista.bottom).level) →
      ∃time output,time≤C*((inputWord state messages degree).length+1)^d ∧
        HaltsAt (advanceProgram core) (inputWord state messages degree) time output ∧
        output.tape.denotes=Turing.Tape.mk₁ ((outputWord (transition core state messages degree)).map bitSymbol) := by
  obtain ⟨C,d,polynomial⟩:=complete_polynomial core
  refine ⟨20*(C+259)^2,(d+1)*2,?_⟩
  intro state messages degree valid received
  obtain ⟨steps,bound,finish,ran,halted,stored⟩:=polynomial state messages degree valid received
  have stackHalt:StackMachine.HaltsAt (complete core).program (inputWord state messages degree) steps finish:=⟨ran,halted⟩
  obtain ⟨time,output,timeBound,executed,tape⟩:=StackMachine.Compiler.compile_halts stackHalt
  refine ⟨time,output,timeBound.trans ?_,executed,?_⟩
  · let N:=(inputWord state messages degree).length+1
    have positive:1≤N:=by dsimp [N];omega
    have linear:N≤N^(d+1):=Nat.le_self_pow (by omega) _
    have one:1≤N^(d+1):=one_le_pow₀ positive
    have raised:=bound.trans (Nat.mul_le_mul_left C (Nat.pow_le_pow_right positive (show d≤d+1 by omega)))
    have base:(inputWord state messages degree).length+254+steps+4≤(C+259)*N^(d+1) := by
      rw [Nat.add_mul]
      dsimp only [N] at linear one raised ⊢
      omega
    calc
      _≤20*((C+259)*N^(d+1))^2:=Nat.mul_le_mul_left 20 (Nat.pow_le_pow_left base 2)
      _= _:=by rw [Nat.mul_pow,←Nat.pow_mul];simp only [Nat.mul_assoc,N]
  · have value:finish.store 1=outputWord (transition core state messages degree) := by rw [stored];rfl
    rw [value] at tape
    exact tape

end Counting.Machine
