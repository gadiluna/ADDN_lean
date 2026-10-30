import Counting.StackAnchorCoefficient
import Counting.GaussianNormalMatrix
import Counting.ExecutableRefinementAnchor

/-! The exact list matrix that the physical anchor constructor must emit.
Node enumeration is the stored DAG order, including for anchor zero. -/
namespace Counting.StackMachine.AnchorCoefficient

theorem coefficient_eq (node : Executable.Node) (parent : Nat) :
    coefficient node parent = (Executable.countFrom node parent : Rat) -
      if node.parent == some parent then (node.degree : Rat) else 0 := by
  unfold coefficient chargedDegree
  split <;> simp

/-- Selected nodes in their physical array order; no anonymity is present. -/
def selectedNodes (nodes : List Executable.Node) (level : Nat) : List Executable.Node :=
  nodes.filter (fun node => node.level == level)

def flowRow (nodes : List Executable.Node) (anchor parent : Nat) : List Rat :=
  (selectedNodes nodes anchor).map (fun node => coefficient node parent) ++ [0]

def leaderRow (nodes : List Executable.Node) (anchor leaders : Nat) : List Rat :=
  (selectedNodes nodes anchor).map (fun node => if node.leader then 1 else 0) ++ [(leaders : Rat)]

def matrix (vista : Executable.Vista) (anchor leaders : Nat) : List (List Rat) :=
  ((Executable.levelNodes vista (anchor-1)).map (flowRow vista.nodes.toList anchor)) ++
    [leaderRow vista.nodes.toList anchor leaders]

theorem range_nodes (vista : Executable.Vista) :
    (List.range vista.nodes.size).map vista.node = vista.nodes.toList := by
  apply List.ext_getElem
  · simp
  · intro i leftBound rightBound
    simp only [List.length_map,List.length_range] at leftBound
    simp [Executable.Vista.node,Array.getElem?_eq_getElem leftBound]

theorem selectedNodes_eq (vista : Executable.Vista) (level : Nat) :
    selectedNodes vista.nodes.toList level =
      (Executable.levelNodes vista level).map vista.node := by
  rw [selectedNodes,←range_nodes]
  simp only [List.filter_map,Executable.levelNodes,Function.comp_def]

theorem matrix_eq_anchorRows (vista : Executable.Vista) (anchor leaders : Nat) :
    matrix vista anchor leaders = GaussianNormalMatrix.equationMatrix
      (Executable.levelNodes vista anchor).length (Executable.anchorRows vista anchor leaders) := by
  rw [GaussianNormalMatrix.equationMatrix_of_sized _ _ (Executable.anchorRows_sized _ _ _)]
  simp [matrix,flowRow,leaderRow,selectedNodes_eq,Executable.anchorRows,coefficient_eq,
    List.map_map,Function.comp_def]

end Counting.StackMachine.AnchorCoefficient
