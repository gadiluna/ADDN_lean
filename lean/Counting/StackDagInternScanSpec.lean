import Counting.StackDagInternLoop
import Counting.DagInternListSpec

namespace Counting.StackMachine.DagUpdate.Intern

theorem scanState_found (query : Executable.Node) (nodes : List Executable.Node) (index : Nat) :
    scanState query nodes true index=(true,index) := by
  induction nodes with
  | nil => rfl
  | cons node nodes ih => simpa [scanState] using ih

theorem scanState_firstIndex (query : Executable.Node) (nodes : List Executable.Node) (index : Nat) :
    scanState query nodes false index=
      ((Executable.firstIndex query nodes).isSome,
        index+(Executable.firstIndex query nodes).getD nodes.length) := by
  induction nodes generalizing index with
  | nil => simp [scanState,Executable.firstIndex]
  | cons node nodes ih =>
    by_cases equal : node=query
    · subst node
      simp [scanState,Executable.firstIndex,scanState_found]
    · have reverse : query≠node := Ne.symm equal
      simp only [scanState,reverse,decide_false,Bool.false_or,Bool.false_eq_true,ite_false]
      rw [ih]
      simp only [Executable.firstIndex,beq_iff_eq,equal,ite_false]
      cases value : Executable.firstIndex query nodes <;> simp [Nat.add_comm,Nat.add_left_comm]

end Counting.StackMachine.DagUpdate.Intern
