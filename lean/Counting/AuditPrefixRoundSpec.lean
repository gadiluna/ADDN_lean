import Counting.AuditPrefixScanState

namespace Counting.StackMachine.AuditPrefix

def scanCheck (vista : Executable.Vista) (candidate start count : Nat) : Bool :=
  (List.range' start count).all (roundCheck vista candidate)

def scanAnchor (vista : Executable.Vista) (start count : Nat) (anchor : Option Nat) : Option Nat :=
  lastMatch (Executable.flat vista) anchor (List.range' (start+1) count)

@[simp] theorem scanCheck_zero (vista : Executable.Vista) (candidate start : Nat) :
    scanCheck vista candidate start 0=true := rfl

@[simp] theorem scanAnchor_zero (vista : Executable.Vista) (start : Nat) (anchor : Option Nat) :
    scanAnchor vista start 0 anchor=anchor := rfl

theorem scanCheck_succ (vista : Executable.Vista) (candidate start count : Nat) :
    scanCheck vista candidate start (count+1)=
      (roundCheck vista candidate start && scanCheck vista candidate (start+1) count) := by
  simp only [scanCheck,List.range'_succ,List.all_cons]

theorem scanAnchor_succ (vista : Executable.Vista) (start count : Nat) (anchor : Option Nat) :
    scanAnchor vista start (count+1) anchor=
      scanAnchor vista (start+1) count (nextAnchor vista start anchor) := by
  simp only [scanAnchor,List.range'_succ,lastMatch,List.foldl_cons,nextAnchor]

/-- The interleaved physical tests are exactly the three literal
conjunctions in the executable prefix. -/
theorem prefixStatus_eq (vista : Executable.Vista) (candidate last : Nat) :
    (rootAccepted vista candidate && scanCheck vista candidate 0 last)=
      ((Executable.levelNodes vista 0).any (fun i=>(vista.node i).leader) &&
        (List.range (last+1)).all (fun level=>decide ((Executable.levelNodes vista level).length≤candidate)) &&
          (List.range last).all (childrenPresent vista)) := by
  have widths : (List.range (last+1)).all (fun level=>decide ((Executable.levelNodes vista level).length≤candidate))=
      (decide ((Executable.levelNodes vista 0).length≤candidate) &&
        (List.range last).all (fun level=>decide ((Executable.levelNodes vista (level+1)).length≤candidate))) := by
    rw [List.range_eq_range',List.range'_succ]
    simp only [List.all_cons,List.range'_eq_map_range,List.all_map,Nat.zero_add,Nat.add_comm,
      Function.comp_def]
  rw [widths]
  apply Bool.eq_iff_iff.mpr
  simp [rootAccepted,scanCheck,←List.range_eq_range',roundCheck,List.all_eq_true,forall_and,and_assoc]

theorem countsPrefix_eq_scan (vista : Executable.Vista) (candidate last : Nat) :
    countsPrefix? vista candidate last=
      if rootAccepted vista candidate && scanCheck vista candidate 0 last then
        scanAnchor vista 0 last none else none := by
  have leader : (countRange vista .leader 0 0 0 vista.nodes.size=0) ↔
      ((Executable.levelNodes vista 0).any (fun i=>(vista.node i).leader))=false := by
    have positive:=countRange_leader_positive vista 0 0
    cases seen:(Executable.levelNodes vista 0).any (fun i=>(vista.node i).leader) with
    | false=>
      have zero : countRange vista .leader 0 0 0 vista.nodes.size=0 := by
        rw [seen] at positive
        simp only [Bool.false_eq_true,iff_false] at positive
        omega
      simp [zero]
    | true=>
      have nonzero : countRange vista .leader 0 0 0 vista.nodes.size≠0:=Nat.ne_of_gt (positive.mpr seen)
      simp [nonzero]
  have flatPred : countFlat vista=Executable.flat vista:=funext (countFlat_eq vista)
  rw [prefixStatus_eq]
  simp only [scanAnchor,Nat.zero_add,lastFlat_eq,countsPrefix?,countRange_full_level,flatPred,leader]
  cases (Executable.levelNodes vista 0).any (fun i=>(vista.node i).leader) <;>
    cases (List.range (last+1)).all (fun level=>decide ((Executable.levelNodes vista level).length≤candidate)) <;>
    cases (List.range last).all (childrenPresent vista) <;> rfl

end Counting.StackMachine.AuditPrefix
