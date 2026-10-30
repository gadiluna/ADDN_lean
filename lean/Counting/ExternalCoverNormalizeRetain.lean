import Counting.ExternalCoverNormalizePrevious

namespace Counting.External.CoverNormalization
open StackMachine StackMachine.Routine StackMachine.EncodingPrograms CoverMachine
set_option backward.isDefEq.respectTransparency false

def emitNew (extra : Nat) (w : RowWorkspace extra) : Routine (extra+46) :=
  sequence (ofProgram (ListPrograms.reverseProgram (extra+46) (w 38) (w 36)))
    (pushBit (w 41) true)

/-- The output stream is maintained in reverse bit order. One unary counter
counts retained rows, and another counts every source row visited. -/
def retainRow (extra : Nat) (w : RowWorkspace extra) : Routine (extra+46) :=
  sequence (branchRoutine (w 22) (clear (w 38)) (emitNew extra w)) (pushBit (w 40) true)

def retained (w : RowWorkspace extra) (store : Fin (extra+48) → List Bool) (seen : Bool) :=
  Function.update (Function.update (Function.update (Function.update (Function.update store
    (w 22) []) (w 38) []) (w 36)
      (if seen then store (w 36) else (store (w 38)).reverse++store (w 36)))
    (w 41) (if seen then store (w 41) else true::store (w 41)))
    (w 40) (true::store (w 40))

theorem retainRow_executes (extra : Nat) (w : RowWorkspace extra)
    (store : Fin (extra+48) → List Bool) (seen : Bool) (flag : store (w 22)=[seen]) :
    ∃ time ≤ 2*(store (w 38)).length+6,
      Executes (retainRow extra w) store time (retained w store seen) := by
  let popped := Function.update store (w 22) []
  cases seen with
  | true =>
    have clearing := clear_executes (w 38) popped
    have word : popped (w 38)=store (w 38) := by simp [popped,w.injective.eq_iff]
    rw [word] at clearing
    let cleaned := Function.update popped (w 38) []
    have branching := branch_executes_true (w 22) (clear (w 38)) (emitNew extra w)
      store cleaned [] ((store (w 38)).length+1) flag clearing
    have pushing := pushBit_executes (w 40) true cleaned
    have final : Function.update cleaned (w 40) (true::cleaned (w 40))=retained w store true := by
      funext r
      by_cases e36 : r=w 36
      · subst r;simp [retained,cleaned,popped,w.injective.eq_iff]
      · by_cases e41 : r=w 41
        · subst r;simp [retained,cleaned,popped,w.injective.eq_iff]
        · simp [retained,cleaned,popped,e36,e41,Function.update_apply,w.injective.eq_iff]
    rw [final] at pushing
    exact ⟨1+((store (w 38)).length+1)+1+1,by omega,branching.sequence pushing⟩
  | false =>
    have reversing := reverse_executes (extra+46) (w 38) (w 36)
      (by simp [w.injective.eq_iff]) popped
    have word : popped (w 38)=store (w 38) := by simp [popped,w.injective.eq_iff]
    rw [word] at reversing
    let reversed := Function.update (Function.update popped (w 38) []) (w 36)
      ((store (w 38)).reverse++popped (w 36))
    have counting := pushBit_executes (w 41) true reversed
    let emitted := Function.update reversed (w 41) (true::reversed (w 41))
    have emitting : Executes (emitNew extra w) popped (2*(store (w 38)).length+1+1+1) emitted :=
      reversing.sequence counting
    have branching := branch_executes_false (w 22) (clear (w 38)) (emitNew extra w)
      store emitted [] (2*(store (w 38)).length+1+1+1) flag emitting
    have pushing := pushBit_executes (w 40) true emitted
    have final : Function.update emitted (w 40) (true::emitted (w 40))=retained w store false := by
      simp [retained,emitted,reversed,popped,w.injective.eq_iff]
    rw [final] at pushing
    exact ⟨1+(2*(store (w 38)).length+1+1+1)+1+1,by omega,branching.sequence pushing⟩

end Counting.External.CoverNormalization
