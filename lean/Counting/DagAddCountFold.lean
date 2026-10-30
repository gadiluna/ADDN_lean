import Counting.DagAddCountSpec

namespace Counting.DagUpdate
set_option backward.isDefEq.respectTransparency false

/-- Emission state before the final pending pair is flushed. -/
def addCountPrefix (index count : Nat) : Bool → List (Nat×Nat) → List (Nat×Nat)×Bool
  | pending,[]=>([],pending)
  | pending,edge::rest=>
    let first:=addCountStep index count pending edge
    let tail:=addCountPrefix index count first.2 rest
    (first.1++tail.1,tail.2)

theorem addCountPrefix_flush (index count : Nat) (pending : Bool) (edges : List (Nat×Nat)) :
    (addCountPrefix index count pending edges).1++
      (if (addCountPrefix index count pending edges).2 then [(index,count)] else [])=
      addCountEntries index count pending edges := by
  induction edges generalizing pending with
  | nil=>rfl
  | cons edge rest ih=>
    simp only [addCountPrefix,addCountEntries,List.append_assoc]
    rw [ih]

theorem addCountPrefix_length (index count : Nat) (pending : Bool) (edges : List (Nat×Nat)) :
    (addCountPrefix index count pending edges).1.length ≤ 2*edges.length := by
  induction edges generalizing pending with
  | nil=>simp [addCountPrefix]
  | cons edge rest ih=>
    have head:=addCountStep_length index count pending edge
    have tail:=ih (addCountStep index count pending edge).2
    simp only [addCountPrefix,List.length_append,List.length_cons]
    omega

end Counting.DagUpdate
