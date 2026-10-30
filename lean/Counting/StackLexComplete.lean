import Counting.StackLexLoop
import Counting.StackRoutineUnary

namespace Counting.StackMachine.Lexicographic
open Routine
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000

def prepareComparison : Routine 14 := sequence (ofProgram (Unary.lengthProgram 13 10 13 12))
  (sequence (pushBit 2 true) (pushBit 3 true))

def finishComparison : Routine 14 := sequence (clear 2) (clear 11)

def compareStreams : Routine 14 := sequence prepareComparison (sequence streamLoop finishComparison)

def comparisonResult (store : Store 14) (left right : List Nat) : Store 14 :=
  Function.update (Function.update (Function.update store 10 []) 11 []) 3 [Executable.lexLE left right]

theorem sequence_natural_length (values : List Nat) :
    values.length≤(Encoding.sequence Encoding.natural values).length := by
  induction values with
  | nil => simp [Encoding.sequence]
  | cons head tail ih =>
    simp only [Encoding.sequence,List.length_cons,List.length_append,Encoding.natural_length]
    omega

theorem prepareComparison_executes (store : Store 14) (left right : List Nat)
    (sourceLeft : store 10=Encoding.sequence Encoding.natural left)
    (sourceRight : store 11=Encoding.sequence Encoding.natural right)
    (empty : ∀ r : Fin 16,r=2 ∨ r=3 ∨ r=12 ∨ r=13 → store r=[]) :
    Executes prepareComparison store (5*(store 10).length+6)
      (loopStore store ⟨left,right,true,true⟩ (List.replicate (store 10).length true)) := by
  have lengthRun := length_executes 13 (10:Fin 16) 13 12 (by decide) (by decide) (by decide)
    store (empty 12 (by simp))
  rw [empty 13 (by simp),List.append_nil] at lengthRun
  let counted := Function.update store 13 (List.replicate (store 10).length true)
  have opened := pushBit_executes (2:Fin 16) true counted
  have openEmpty : counted 2=[] := by simp [counted,empty]
  rw [openEmpty] at opened
  let marked := Function.update counted 2 [true]
  have answer := pushBit_executes (3:Fin 16) true marked
  have answerEmpty : marked 3=[] := by simp [marked,counted,empty]
  rw [answerEmpty] at answer
  have final : Function.update marked 3 [true]=
      loopStore store ⟨left,right,true,true⟩ (List.replicate (store 10).length true) := by
    funext r
    fin_cases r <;> simp [loopStore,stateStore,marked,counted,sourceLeft,sourceRight]
  rw [final] at answer
  convert lengthRun.sequence (opened.sequence answer) using 1 <;> rfl

theorem finishComparison_executes (store : Store 14) (value : LexState)
    (emptyLeft : value.left=[]) (empty : store 2=[] ∧ store 13=[]) :
    Executes finishComparison (loopStore store value [])
      ((Encoding.sequence Encoding.natural value.right).length+4)
      (Function.update (Function.update (Function.update store 10 []) 11 []) 3 [value.answer]) := by
  have first := clear_executes (2:Fin 16) (loopStore store value [])
  have openAt : loopStore store value [] 2=[value.unresolved] := by simp [loopStore,stateStore]
  rw [openAt,List.length_singleton] at first
  let erased := Function.update (loopStore store value []) 2 []
  have second := clear_executes (11:Fin 16) erased
  have rightAt : erased 11=Encoding.sequence Encoding.natural value.right := by simp [erased,loopStore,stateStore]
  rw [rightAt] at second
  have final : Function.update erased 11 []=
      Function.update (Function.update (Function.update store 10 []) 11 []) 3 [value.answer] := by
    funext r
    fin_cases r <;> simp [erased,loopStore,stateStore,emptyLeft,Encoding.sequence,empty]
  rw [final] at second
  convert first.sequence second using 1 <;> first | rfl | omega

/-- An actual bounded parser loop compares complete self-delimiting numeric
sequences. Its bound is quadratic in the two encoded input lengths, and every
scratch register is restored. -/
theorem compareStreams_executes (store : Store 14) (left right : List Nat)
    (sourceLeft : store 10=Encoding.sequence Encoding.natural left)
    (sourceRight : store 11=Encoding.sequence Encoding.natural right)
    (empty : ∀ r : Fin 16,r.val≤9 ∨ r=12 ∨ r=13 → store r=[]) :
    ∃ time≤100*((store 10).length+(store 11).length+1)^2,
      Executes compareStreams store time (comparisonResult store left right) := by
  let initial : LexState := ⟨left,right,true,true⟩
  let count := (store 10).length
  let result := (LexState.advance)^[count] initial
  have enough : left.length≤count := by simpa only [count,sourceLeft] using sequence_natural_length left
  have finished := LexState.iterate_answer initial (by simp [initial,LexState.Valid]) count enough
  have finishLeft : result.left=[] := finished.1
  have finishAnswer : result.answer=Executable.lexLE left right := finished.2
  have first := prepareComparison_executes store left right sourceLeft sourceRight (by
    intro r allowed
    fin_cases r <;> simp_all)
  have second := streamLoop_executes store initial (List.replicate count true) (by
    intro r allowed
    fin_cases r <;> simp_all)
  simp only [List.length_replicate] at second
  have third := finishComparison_executes store result finishLeft
    ⟨empty 2 (by simp),empty 13 (by simp)⟩
  rw [finishAnswer] at third
  have run := first.sequence (second.sequence third)
  refine ⟨_,?_,run⟩
  have loopBound := streamLoopCost_le count initial
  have outputBound := LexState.iterate_encodedLength initial count
  have rightBound : (Encoding.sequence Encoding.natural result.right).length ≤ initial.encodedLength := by
    unfold LexState.encodedLength at outputBound ⊢
    dsimp only [result]
    omega
  have total : initial.encodedLength=(store 10).length+(store 11).length := by
    simp [initial,LexState.encodedLength,sourceLeft,sourceRight]
  rw [total] at loopBound rightBound
  dsimp only [count] at loopBound ⊢
  nlinarith

end Counting.StackMachine.Lexicographic
