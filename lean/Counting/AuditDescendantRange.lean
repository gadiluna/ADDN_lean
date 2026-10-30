import Counting.AuditDescendantSpec

namespace Counting.Executable

def auditAncestor (vista : Vista) (weights : Array Nat) (anchor last ancestor : Nat) : Bool :=
  if (vista.node ancestor).level=anchor then auditDescendantAt vista weights anchor last ancestor else true

def auditDescendantRange (vista : Vista) (weights : Array Nat) (anchor last start count : Nat) : Bool :=
  (List.range' start count).all (auditAncestor vista weights anchor last)

@[simp] theorem auditDescendantRange_zero (vista : Vista) (weights : Array Nat) (anchor last start : Nat) :
    auditDescendantRange vista weights anchor last start 0=true := rfl

theorem auditDescendantRange_succ (vista : Vista) (weights : Array Nat) (anchor last start count : Nat) :
    auditDescendantRange vista weights anchor last start (count+1)=
      (auditAncestor vista weights anchor last start &&
        auditDescendantRange vista weights anchor last (start+1) count) := by
  simp only [auditDescendantRange,List.range'_succ,List.all_cons]

theorem auditDescendantRange_full (vista : Vista) (weights : Array Nat) (anchor last : Nat) :
    auditDescendantRange vista weights anchor last 0 vista.nodes.size=auditDescendants vista weights anchor last := by
  rw [auditDescendantRange,auditDescendants,List.range_eq_range']
  rfl

end Counting.Executable
