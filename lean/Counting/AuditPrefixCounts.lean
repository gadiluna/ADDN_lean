import Counting.StackAuditPrefixSelect

namespace Counting.StackMachine.AuditPrefix

def countRange (vista : Executable.Vista) (mode : HeaderMode) (level parent start count : Nat) : Nat :=
  ((List.range' start count).filter (fun i=>nodeMatches mode (vista.node i) level parent)).length

@[simp] theorem countRange_zero (vista : Executable.Vista) (mode : HeaderMode) (level parent start : Nat) :
    countRange vista mode level parent start 0=0 := rfl

theorem countRange_succ (vista : Executable.Vista) (mode : HeaderMode) (level parent start count : Nat) :
    countRange vista mode level parent start (count+1)=
      (if nodeMatches mode (vista.node start) level parent then 1 else 0)+
        countRange vista mode level parent (start+1) count := by
  simp only [countRange,List.range'_succ,List.filter_cons]
  cases nodeMatches mode (vista.node start) level parent <;> simp [Nat.add_comm]

theorem countRange_le (vista : Executable.Vista) (mode : HeaderMode) (level parent start count : Nat) :
    countRange vista mode level parent start count ≤ count :=
  (List.length_filter_le _ _).trans_eq List.length_range'

theorem countRange_full_level (vista : Executable.Vista) (level parent : Nat) :
    countRange vista .level level parent 0 vista.nodes.size=(Executable.levelNodes vista level).length := by
  simp only [countRange,←List.range_eq_range',Executable.levelNodes,nodeMatches,headerPredicate]
  congr 2

theorem parentCode_eq_succ (node : Executable.Node) (parent : Nat) :
    DagValidation.parentCode node=parent+1 ↔ node.parent=some parent := by
  cases current:node.parent <;> simp [DagValidation.parentCode,current]

theorem countRange_full_children (vista : Executable.Vista) (level parent : Nat) :
    countRange vista .child level (parent+1) 0 vista.nodes.size=
      (Executable.children vista parent level).length := by
  unfold countRange Executable.children Executable.levelNodes
  rw [←List.range_eq_range',List.filter_filter]
  congr 2
  funext index
  apply Bool.eq_iff_iff.mpr
  simp [nodeMatches,headerPredicate,parentCode_eq_succ,and_comm]

theorem countRange_full_leaders (vista : Executable.Vista) (level parent : Nat) :
    countRange vista .leader level parent 0 vista.nodes.size=
      ((Executable.levelNodes vista level).filter (fun i=>(vista.node i).leader)).length := by
  unfold countRange Executable.levelNodes
  rw [←List.range_eq_range',List.filter_filter]
  congr 2
  funext index
  apply Bool.eq_iff_iff.mpr
  simp [nodeMatches,headerPredicate,and_comm]

theorem countRange_leader_positive (vista : Executable.Vista) (level parent : Nat) :
    0<countRange vista .leader level parent 0 vista.nodes.size ↔
      (Executable.levelNodes vista level).any (fun i=>(vista.node i).leader)=true := by
  rw [countRange_full_leaders]
  simp [List.length_pos_iff,List.any_eq_true]

end Counting.StackMachine.AuditPrefix
