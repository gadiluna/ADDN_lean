import Counting.StackAnchorMatrixLoop

namespace Counting.StackMachine.AnchorMatrix

theorem generatedRows_range (vista : Executable.Vista) (anchor previous start : Nat)
    (remaining : List Executable.Node)
    (matched : ∀ i (inside : i<remaining.length),remaining[i]=vista.node (start+i)) :
    generatedRows vista.nodes.toList anchor previous start remaining=
      ((List.range' start remaining.length).filter (fun i=>(vista.node i).level==previous)).map
        (AnchorCoefficient.flowRow vista.nodes.toList anchor) := by
  induction remaining generalizing start with
  | nil => simp [generatedRows]
  | cons node rest ih =>
    have first : node=vista.node start := by
      have result := matched 0 (by simp)
      change node=vista.node (start+0) at result
      simpa only [Nat.add_zero] using result
    have tails : ∀ i (inside : i<rest.length),rest[i]=vista.node ((start+1)+i) := by
      intro i inside
      have equality := matched (i+1) (by simp only [List.length_cons];omega)
      simpa only [List.getElem_cons_succ,show start+(i+1)=start+1+i by omega] using equality
    rw [generatedRows,ih (start+1) tails,List.length_cons,List.range'_succ]
    by_cases equal : node.level=previous
    · simp [←first,equal]
    · simp [←first,equal]

/-- The outer scan uses exactly the physical parent indices selected by
`Executable.levelNodes`; it never groups or reorders rows by anonymity. -/
theorem generatedRows_all (vista : Executable.Vista) (anchor previous : Nat) :
    generatedRows vista.nodes.toList anchor previous 0 vista.nodes.toList=
      (Executable.levelNodes vista previous).map (AnchorCoefficient.flowRow vista.nodes.toList anchor) := by
  have result := generatedRows_range vista anchor previous 0 vista.nodes.toList (by
    intro i inside
    simp only [Array.length_toList] at inside
    simp [Executable.Vista.node,Array.getElem?_eq_getElem inside])
  simpa only [Array.length_toList,←List.range_eq_range',Executable.levelNodes] using result

end Counting.StackMachine.AnchorMatrix
