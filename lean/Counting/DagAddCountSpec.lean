import Counting.Executable

namespace Counting.DagUpdate

/-- A pending update emits at most two sparse entries at a time. The
pending flag becomes false after the first insertion or equal index. -/
def addCountStep (index count : Nat) (pending : Bool) (edge : Nat×Nat) : List (Nat×Nat)×Bool :=
  if pending then
    if index=edge.1 then ([(edge.1,edge.2+count)],false)
    else if index < edge.1 then ([(index,count),edge],false)
    else ([edge],true)
  else ([edge],false)

def addCountEntries (index count : Nat) : Bool → List (Nat×Nat) → List (Nat×Nat)
  | pending,[]=>if pending then [(index,count)] else []
  | pending,edge::rest=>
    let next:=addCountStep index count pending edge
    next.1++addCountEntries index count next.2 rest

theorem addCountEntries_inactive (index count : Nat) (edges : List (Nat×Nat)) :
    addCountEntries index count false edges=edges := by
  induction edges with
  | nil=>rfl
  | cons edge rest ih=>simp [addCountEntries,addCountStep,ih]

theorem addCountEntries_active (index count : Nat) (positive : count≠0) (edges : List (Nat×Nat)) :
    addCountEntries index count true edges=Executable.addCount index count edges := by
  induction edges with
  | nil=>simp [addCountEntries,Executable.addCount,positive]
  | cons edge rest ih=>
    rcases edge with ⟨i,c⟩
    by_cases equal : index=i
    · simp [addCountEntries,addCountStep,Executable.addCount,positive,equal,addCountEntries_inactive]
    · by_cases smaller : index < i
      · simp [addCountEntries,addCountStep,Executable.addCount,positive,equal,smaller,addCountEntries_inactive]
      · simp [addCountEntries,addCountStep,Executable.addCount,positive,equal,smaller,ih]

theorem addCountEntries_exact (index count : Nat) (edges : List (Nat×Nat)) :
    addCountEntries index count (decide (count≠0)) edges=Executable.addCount index count edges := by
  by_cases zero : count=0
  · subst count
    cases edges <;> simp [Executable.addCount,addCountEntries_inactive]
  · simpa only [zero,ne_eq,not_false_eq_true,decide_true] using addCountEntries_active index count zero edges

theorem addCountStep_length (index count : Nat) (pending : Bool) (edge : Nat×Nat) :
    (addCountStep index count pending edge).1.length ≤ 2 := by
  simp only [addCountStep]
  split
  · split
    · simp
    · split <;> simp
  · simp

end Counting.DagUpdate
