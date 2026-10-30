import Counting.StackDagReferenceNodes

namespace Counting.StackMachine.DagValidation

def coverRange (nodes : List Executable.Node) : Nat → Nat → Bool
  | _,0=>true
  | target,count+1=>(!noTableReference target nodes) && coverRange nodes (target+1) count

theorem coverRange_iff (nodes : List Executable.Node) (start count : Nat) :
    coverRange nodes start count=true ↔
      ∀ target,start≤target → target<start+count → noTableReference target nodes=false := by
  induction count generalizing start with
  | zero=>
    simp only [coverRange,Nat.add_zero,true_iff]
    intro target lower upper
    omega
  | succ count ih=>
    rw [coverRange,Bool.and_eq_true,ih]
    simp only [Bool.not_eq_true']
    constructor
    · rintro ⟨first,rest⟩ target lower upper
      by_cases same : target=start
      · simpa only [same] using first
      · exact rest target (by omega) (by omega)
    · intro all
      exact ⟨all start le_rfl (by omega),fun target lower upper=>all target (by omega) (by omega)⟩

end Counting.StackMachine.DagValidation
