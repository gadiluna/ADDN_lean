import Counting.ExternalCoverMatchIndex
import Counting.StackBooleanFold

namespace Counting.External.CoverVerification
open StackMachine StackMachine.Routine SATVerification CoverMachine
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

/-- Consume one encoded index and OR its equality with the query into register22. -/
def matchAtom (extra : Nat) (w : RowWorkspace extra) : Routine (extra+46) :=
  sequence (matchIndex extra w) (BooleanFold.single .disjunction (w 21) (w 22))

theorem matchAtom_executes (extra : Nat) (w : RowWorkspace extra)
    (store : Fin (extra+48) → List Bool) (index : Nat) (accepted value : Bool)
    (suffix tail accumulatorTail : List Bool)
    (source : store (w 0)=Encoding.natural.encode index++suffix)
    (status : store (w 1)=accepted::tail) (accumulated : store (w 22)=value::accumulatorTail)
    (empty : ∀ i∈matchScratch,store (w i)=[]) :
    ∃ time ≤ 110*((store (w 0)).length+(store (w 38)).length+1),
      Executes (matchAtom extra w) store time
        (Function.update (Function.update store (w 0) suffix) (w 22)
          ((value || decide (Encoding.natural.encode index=store (w 38)))::accumulatorTail)) := by
  obtain ⟨readTime,readBound,reading⟩ := matchIndex_executes extra w store index accepted suffix tail source status empty
  let bit := decide (Encoding.natural.encode index=store (w 38))
  let read := Function.update (Function.update store (w 0) suffix) (w 21) (bit::store (w 21))
  have folding := BooleanFold.single_executes .disjunction (w 21) (w 22)
    (by simp [w.injective.eq_iff]) read bit value (store (w 21)) accumulatorTail
    (by simp [read]) (by simp [read,w.injective.eq_iff,accumulated])
  have final : BooleanFold.updated (w 21) (w 22) read (store (w 21))
      (BooleanFold.operation .disjunction value bit) accumulatorTail=
      Function.update (Function.update store (w 0) suffix) (w 22) ((value || bit)::accumulatorTail) := by
    funext r
    by_cases e : r=w 21
    · subst r;simp [BooleanFold.updated,BooleanFold.operation,read,w.injective.eq_iff]
    · simp [BooleanFold.updated,BooleanFold.operation,read,e,Function.update_apply]
  rw [final] at folding
  exact ⟨readTime+1+3,by omega,reading.sequence folding⟩

end Counting.External.CoverVerification
