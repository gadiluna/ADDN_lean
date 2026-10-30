import Counting.ProtocolStateEncoding
import Counting.StackRoutineMove
import Counting.StackEncodingBranch
import Counting.StackRoutineClean
import Counting.StackCompilerComplete

namespace Counting.StackMachine.ProtocolInitialize
open Routine EncodingPrograms Executable

def inputWord (leaders : Nat) (leader : Bool) : List Bool :=
  leader::Encoding.natural.encode leaders

def initialViewWord (leader : Bool) : List Bool :=
  Encoding.frame (Encoding.vista.encode (initialVista leader))

def initialOutputWord : List Bool :=
  Encoding.frame ((Encoding.optional Encoding.natural).encode none)

def branch (leader : Bool) : Routine 1 :=
  sequence (prepend 1 (initialViewWord leader))
    (sequence (move 0 0 1 2) (prepend 1 initialOutputWord))

def complete : Routine 1 := branchRoutine 0 (branch true) (branch false)

theorem branch_executes (leaders : Nat) (leader : Bool) :
    ∃ time ≤ 100*((Encoding.natural.encode leaders).length+1),
      Executes (branch leader) (inputStore 1 (Encoding.natural.encode leaders)) time
        (outputStore 1 (ProtocolAdvance.stateWord (initialState leaders leader))) := by
  let initial := inputStore 1 (Encoding.natural.encode leaders)
  have a := prepend_executes (registers:=1) 1 (initialViewWord leader) initial
  rw [show initial 1=[] by rfl,List.append_nil] at a
  let first := Function.update initial 1 (initialViewWord leader)
  have b := move_executes 0 0 1 2 (by decide) (by decide) (by decide) first
    (by simp [first,initial,inputStore])
  rw [show first 0=Encoding.natural.encode leaders by simp [first,initial,inputStore],
    show first 1=initialViewWord leader by simp [first]] at b
  let second := Function.update (Function.update first 1
    (Encoding.natural.encode leaders++initialViewWord leader)) 0 []
  have c := prepend_executes (registers:=1) 1 initialOutputWord second
  have sourceAt : second 1=Encoding.natural.encode leaders++initialViewWord leader := by simp [second]
  rw [sourceAt] at c
  have word : initialOutputWord++(Encoding.natural.encode leaders++initialViewWord leader)=
      ProtocolAdvance.stateWord (initialState leaders leader) := by
    rw [ProtocolAdvance.stateWord_fields]
    rfl
  rw [word] at c
  have final : Function.update second 1 (ProtocolAdvance.stateWord (initialState leaders leader))=
      outputStore 1 (ProtocolAdvance.stateWord (initialState leaders leader)) := by
    funext r;fin_cases r <;> simp [second,first,initial,inputStore,outputStore]
  rw [final] at c
  have viewBound : (initialViewWord leader).length ≤ 30 := by cases leader <;> decide
  have outputLength : initialOutputWord.length=3 := by decide
  refine ⟨_,?_,a.sequence (b.sequence c)⟩
  omega

/-- Initialize the actual serialized local state from only the known
leader count and this agent's leader bit. All three registers are accounted
for, and the input is consumed. -/
theorem complete_executes (leaders : Nat) (leader : Bool) :
    ∃ time ≤ 100*((inputWord leaders leader).length+1),
      Executes complete (inputStore 1 (inputWord leaders leader)) time
        (outputStore 1 (ProtocolAdvance.stateWord (initialState leaders leader))) := by
  obtain ⟨time,bound,run⟩ := branch_executes leaders leader
  have popped : Function.update (inputStore 1 (inputWord leaders leader)) 0 (Encoding.natural.encode leaders)=
      inputStore 1 (Encoding.natural.encode leaders) := by
    funext r;by_cases r0:r=0 <;> simp [inputStore,r0]
  have step : Executes complete (inputStore 1 (inputWord leaders leader)) (1+time)
      (outputStore 1 (ProtocolAdvance.stateWord (initialState leaders leader))) := by
    cases leader with
    | false =>
      exact branch_executes_false 0 (branch true) (branch false) _ _ _ time rfl (by rw [popped];exact run)
    | true =>
      exact branch_executes_true 0 (branch true) (branch false) _ _ _ time rfl (by rw [popped];exact run)
  exact ⟨_,by simp only [inputWord,List.length_cons];omega,step⟩

end Counting.StackMachine.ProtocolInitialize

namespace Counting.Machine
open StackMachine.ProtocolInitialize

def initializeStateProgram : Program := StackMachine.Compiler.compile complete.program

/-- Initial state construction also has charged physical running time; it
requires neither the population nor an agent identifier. -/
theorem initializeState_clean (leaders : Nat) (leader : Bool) :
    ∃ time output,time ≤ 20*106^2*((inputWord leaders leader).length+1)^2 ∧
      HaltsAt initializeStateProgram (inputWord leaders leader) time output ∧
      output.tape.denotes=Turing.Tape.mk₁
        ((StackMachine.ProtocolAdvance.stateWord (Executable.initialState leaders leader)).map bitSymbol) := by
  obtain ⟨steps,bound,last,ran,halted,stored⟩ := complete_executes leaders leader
  have halts : StackMachine.HaltsAt complete.program (inputWord leaders leader) steps last := ⟨ran,halted⟩
  obtain ⟨time,output,cost,execution,tape⟩ := StackMachine.Compiler.compile_halts halts
  refine ⟨time,output,cost.trans ?_,execution,?_⟩
  · have base : (inputWord leaders leader).length+1+steps+4 ≤
        106*((inputWord leaders leader).length+1) := by omega
    calc
      _ ≤ 20*(106*((inputWord leaders leader).length+1))^2 :=
        Nat.mul_le_mul_left 20 (Nat.pow_le_pow_left base 2)
      _ = _ := by ring
  · rw [stored] at tape
    exact tape

theorem initializeState_population_bound (leaders population : Nat) (leader : Bool)
    (bounded : leaders ≤ population) :
    ∃ time output,time ≤ 20*106^2*9*(population+1)^2 ∧
      HaltsAt initializeStateProgram (inputWord leaders leader) time output ∧
      output.tape.denotes=Turing.Tape.mk₁
        ((StackMachine.ProtocolAdvance.stateWord (Executable.initialState leaders leader)).map bitSymbol) := by
  obtain ⟨time,output,cost,halts,tape⟩ := initializeState_clean leaders leader
  have size : leaders.size ≤ population := (Nat.size_le.mpr Nat.lt_two_pow_self).trans bounded
  have input : (inputWord leaders leader).length+1 ≤ 3*(population+1) := by
    simp only [inputWord,List.length_cons,Encoding.natural_length]
    omega
  have scaled := Nat.mul_le_mul_left (20*106^2) (Nat.pow_le_pow_left input 2)
  refine ⟨time,output,cost.trans (scaled.trans_eq ?_),halts,tape⟩
  ring

end Counting.Machine

