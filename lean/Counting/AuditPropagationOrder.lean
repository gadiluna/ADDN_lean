import Counting.ExecutableRefinementWeights

namespace Counting.StackMachine.AuditPropagation

def anchorIndices (anchor start : Nat) : List Executable.Node → List Nat
  | [] => []
  | node::nodes => if node.level=anchor then start::anchorIndices anchor (start+1) nodes
      else anchorIndices anchor (start+1) nodes

def assignScan (anchor start : Nat) : List Executable.Node → List Nat → Array Nat → Array Nat
  | [],_,weights => weights
  | node::nodes,values,weights =>
      if node.level=anchor then match values with
        | [] => assignScan anchor (start+1) nodes [] weights
        | value::values => assignScan anchor (start+1) nodes values (weights.setIfInBounds start value)
      else assignScan anchor (start+1) nodes values weights

theorem assignScan_empty (anchor start : Nat) (nodes : List Executable.Node) (weights : Array Nat) :
    assignScan anchor start nodes [] weights=weights := by
  induction nodes generalizing start with
  | nil => rfl
  | cons node nodes ih => simp [assignScan,ih]

theorem assignScan_eq_entries (anchor start : Nat) (nodes : List Executable.Node)
    (values : List Nat) (weights : Array Nat) :
    assignScan anchor start nodes values weights=
      Executable.assignEntries ((anchorIndices anchor start nodes).zip values) weights := by
  induction nodes generalizing start values weights with
  | nil => rfl
  | cons node nodes ih =>
    by_cases selected : node.level=anchor
    · cases values with
      | nil => simp [assignScan_empty,Executable.assignEntries]
      | cons value values =>
        simpa only [assignScan,selected,if_true,anchorIndices,List.zip_cons_cons,
          Executable.assignEntries,List.foldl_cons,Array.set!_eq_setIfInBounds] using
          ih (start+1) values (weights.setIfInBounds start value)
    · simpa only [assignScan,selected,if_false,anchorIndices] using ih (start+1) values weights

theorem anchorIndices_range (vista : Executable.Vista) (anchor start : Nat) (nodes : List Executable.Node)
    (matched : ∀ i (inside : i<nodes.length),nodes[i]=vista.node (start+i)) :
    anchorIndices anchor start nodes=
      (List.range' start nodes.length).filter (fun i=>(vista.node i).level==anchor) := by
  induction nodes generalizing start with
  | nil => rfl
  | cons node nodes ih =>
    have first : node=vista.node start := by
      have result := matched 0 (by simp)
      simpa only [List.getElem_cons_zero,Nat.add_zero] using result
    have tail : ∀ i (inside : i<nodes.length),nodes[i]=vista.node ((start+1)+i) := by
      intro i inside
      have result := matched (i+1) (by simp only [List.length_cons];omega)
      simpa only [List.getElem_cons_succ,show start+(i+1)=start+1+i by omega] using result
    rw [anchorIndices,ih (start+1) tail,List.length_cons,List.range'_succ]
    by_cases selected : node.level=anchor <;> simp [←first,selected]

theorem anchorIndices_vista (vista : Executable.Vista) (anchor : Nat) :
    anchorIndices anchor 0 vista.nodes.toList=Executable.levelNodes vista anchor := by
  have result := anchorIndices_range vista anchor 0 vista.nodes.toList (by
    intro i inside
    simp only [Array.length_toList] at inside
    simp [Executable.Vista.node,Array.getElem?_eq_getElem inside])
  simpa only [Array.length_toList,←List.range_eq_range',Executable.levelNodes] using result

/-- The physical scan's order agrees with the exact anchor zip in the
executable, also for short or excess natural vectors. -/
theorem assignScan_vista (vista : Executable.Vista) (anchor : Nat) (natural : Array Nat) (weights : Array Nat) :
    assignScan anchor 0 vista.nodes.toList natural.toList weights=
      Executable.assignEntries ((Executable.levelNodes vista anchor).zip natural.toList) weights := by
  rw [assignScan_eq_entries,anchorIndices_vista]

end Counting.StackMachine.AuditPropagation
