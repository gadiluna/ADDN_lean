import Counting.StackAuditPrefixChildSelect
import Counting.DagSemanticsTransport

namespace Counting.StackMachine.AuditPrefix

def childRange (vista : Executable.Vista) (level start count : Nat) : Bool×Bool :=
  ((List.range' start count).all (fun i=>(childPredicates vista level i).1),
   (List.range' start count).all (fun i=>(childPredicates vista level i).2))

@[simp] theorem childRange_zero (vista : Executable.Vista) (level start : Nat) :
    childRange vista level start 0=(true,true) := rfl

theorem childRange_succ (vista : Executable.Vista) (level start count : Nat) :
    childRange vista level start (count+1)=
      ((childPredicates vista level start).1 && (childRange vista level (start+1) count).1,
       (childPredicates vista level start).2 && (childRange vista level (start+1) count).2) := by
  simp only [childRange,List.range'_succ,List.all_cons]

theorem childRange_present (vista : Executable.Vista) (level : Nat) :
    (childRange vista level 0 vista.nodes.size).1=childrenPresent vista level := by
  simp only [childRange,←List.range_eq_range',childrenPresent]
  congr 1
  funext i
  simp only [childPredicates]
  split <;> rfl

/-- At an actual level of a valid DAG the required nonempty parent level
is derived from its bottom history. The all-singleton child test is then
exactly the executable flat-level predicate. -/
theorem childRange_flat (vista : Executable.Vista) (valid : vista.valid=true) (level : Nat)
    (within : level≤(vista.node vista.bottom).level) :
    (childRange vista level 0 vista.nodes.size).2=Executable.flat vista (level+1) := by
  have nonempty:=Executable.levelNodes_nonempty_of_le vista valid level within
  have positive : 0<countRange vista .level level 0 0 vista.nodes.size := by
    rw [countRange_full_level]
    exact List.length_pos_iff.mpr nonempty
  rw [←countFlat_eq]
  simp only [countFlat,Nat.add_sub_cancel_right,decide_true,positive]
  simp only [childRange,←List.range_eq_range']
  congr 1
  funext i
  simp only [childPredicates]
  split <;> rfl

end Counting.StackMachine.AuditPrefix
