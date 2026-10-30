import Counting.StackLexShort
import Counting.StackLexState

namespace Counting.StackMachine.Lexicographic
open Routine
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

def stateStore (store : Store 14) (value : LexState) : Store 14 :=
  Function.update (Function.update (Function.update (Function.update store
    10 (Encoding.sequence Encoding.natural value.left))
    11 (Encoding.sequence Encoding.natural value.right)) 2 [value.unresolved]) 3 [value.answer]

def streamStep : Routine 14 :=
  branchNonempty 10 (branchNonempty 11 readPair shortRight) (skip 14)

def streamStepCost (value : LexState) : Nat :=
  match value.left,value.right with
  | [],_ => 1
  | _::_,[] => (Encoding.sequence Encoding.natural value.left).length+
      (if value.unresolved then 18 else 9)
  | a::_,b::_ => readPairCost a b value.unresolved+6

private theorem branchNonempty_nonempty {registers : Nat} (source : Fin (registers+2))
    (yes no : Routine registers) (store result : Store registers) (time : Nat)
    (nonempty : store source≠[]) (executed : Executes yes store time result) :
    Executes (branchNonempty source yes no) store (time+3) result := by
  cases h : store source with
  | nil => exact False.elim (nonempty h)
  | cons bit rest => exact branchNonempty_cons source yes no store result bit rest time h executed

private theorem encoded_cons_nonempty (head : Nat) (tail : List Nat) :
    Encoding.sequence Encoding.natural (head::tail)≠[] := by
  intro empty
  have lengths := congrArg List.length empty
  simp only [Encoding.sequence,List.length_append,Encoding.natural,Encoding.frame_length,List.length_nil] at lengths
  omega

/-- One loop body compares the first remaining numeric fields, or records
that the right key ended. The empty-left case takes one real dispatch step. -/
theorem streamStep_executes (store : Store 14) (value : LexState)
    (empty : ∀ r : Fin 16,r=0 ∨ r=1 ∨ (4≤r.val ∧ r.val≤9) ∨ r=12 → store r=[]) :
    Executes streamStep (stateStore store value) (streamStepCost value) (stateStore store value.advance) := by
  rcases value with ⟨left,right,unresolved,answer⟩
  cases left with
  | nil =>
    exact branchNonempty_empty (10:Fin 16) (branchNonempty 11 readPair shortRight) (skip 14)
      _ _ 0 (by simp [stateStore,Encoding.sequence]) (skip_executes _)
  | cons a left =>
    have firstNonempty : stateStore store ⟨a::left,right,unresolved,answer⟩ 10≠[] := by
      simpa [stateStore] using encoded_cons_nonempty a left
    cases right with
    | nil =>
      have short := shortRight_executes (stateStore store ⟨a::left,[],unresolved,answer⟩) unresolved answer
        (by simp [stateStore]) (by simp [stateStore])
      have final : shortResult (stateStore store ⟨a::left,[],unresolved,answer⟩) unresolved answer=
          stateStore store (LexState.advance ⟨a::left,[],unresolved,answer⟩) := by
        funext r
        fin_cases r <;> simp [shortResult,stateStore,LexState.advance,Encoding.sequence]
      rw [final] at short
      have choose := branchNonempty_empty (11:Fin 16) readPair shortRight _ _ _
        (by simp [stateStore,Encoding.sequence]) short
      have outer := branchNonempty_nonempty (10:Fin 16) (branchNonempty 11 readPair shortRight) (skip 14)
        _ _ _ firstNonempty choose
      convert outer using 1 <;> first | rfl | (cases unresolved <;> simp [streamStepCost,stateStore] <;> omega)
    | cons b right =>
      have compare := readPair_executes (stateStore store ⟨a::left,b::right,unresolved,answer⟩) a b
        (Encoding.sequence Encoding.natural left) (Encoding.sequence Encoding.natural right) unresolved answer
        (by simp [stateStore,Encoding.sequence]) (by simp [stateStore,Encoding.sequence])
        (by simp [stateStore]) (by simp [stateStore]) (by
          intro r allowed
          fin_cases r <;> simp_all [stateStore])
      have final : readPairResult (stateStore store ⟨a::left,b::right,unresolved,answer⟩)
          a b (Encoding.sequence Encoding.natural left) (Encoding.sequence Encoding.natural right) unresolved answer=
          stateStore store (LexState.advance ⟨a::left,b::right,unresolved,answer⟩) := by
        funext r
        fin_cases r <;> simp [readPairResult,stateStore,LexState.advance]
      rw [final] at compare
      have secondNonempty : stateStore store ⟨a::left,b::right,unresolved,answer⟩ 11≠[] := by
        simpa [stateStore] using encoded_cons_nonempty b right
      have choose := branchNonempty_nonempty (11:Fin 16) readPair shortRight _ _ _ secondNonempty compare
      have outer := branchNonempty_nonempty (10:Fin 16) (branchNonempty 11 readPair shortRight) (skip 14)
        _ _ _ firstNonempty choose
      convert outer using 1 <;> rfl

theorem streamStepCost_le (value : LexState) : streamStepCost value≤60*(value.encodedLength+1) := by
  rcases value with ⟨left,right,unresolved,answer⟩
  cases left with
  | nil => simp [streamStepCost,LexState.encodedLength];omega
  | cons a left =>
    cases right with
    | nil => cases unresolved <;> simp [streamStepCost,LexState.encodedLength,Encoding.sequence] <;> omega
    | cons b right =>
      have bound := readPairCost_le a b unresolved
      simp only [streamStepCost,LexState.encodedLength,Encoding.sequence,List.length_append,
        Encoding.natural,Encoding.frame_length]
      omega

end Counting.StackMachine.Lexicographic
