import Counting.StackRealizabilityIncidenceLoop

namespace Counting.StackMachine.RealizabilityCheck

def incomingRows (nodes : List Executable.Node) (width : Nat) : List Bool :=
  nodes.flatMap (fun node => incomingRowValues node 0 width)

def parentRows (nodes : List Executable.Node) (width : Nat) : List Bool :=
  nodes.flatMap (fun node => parentRowValues node 0 width)

@[simp] theorem incomingRows_length (nodes : List Executable.Node) (width : Nat) :
    (incomingRows nodes width).length=nodes.length*width := by
  induction nodes with
  | nil => simp [incomingRows]
  | cons node nodes ih =>
    simp only [incomingRows,List.flatMap_cons,List.length_append,incomingRowValues_length,List.length_cons]
    change width+(incomingRows nodes width).length=(nodes.length+1)*width
    rw [ih]
    ring

@[simp] theorem parentRows_length (nodes : List Executable.Node) (width : Nat) :
    (parentRows nodes width).length=nodes.length*width := by
  induction nodes with
  | nil => simp [parentRows]
  | cons node nodes ih =>
    simp only [parentRows,List.flatMap_cons,List.length_append,parentRowValues_length,List.length_cons]
    change width+(parentRows nodes width).length=(nodes.length+1)*width
    rw [ih]
    ring

def incomingMatrixValues (nodes : List Executable.Node) : List Bool :=
  incomingRows nodes (nodes.length+1) ++ List.replicate (nodes.length+1) false

def parentMatrixValues (nodes : List Executable.Node) : List Bool :=
  parentRows nodes (nodes.length+1) ++ List.replicate (nodes.length+1) false

@[simp] theorem incomingMatrixValues_length (nodes : List Executable.Node) :
    (incomingMatrixValues nodes).length=(nodes.length+1)^2 := by
  simp [incomingMatrixValues]
  ring

@[simp] theorem parentMatrixValues_length (nodes : List Executable.Node) :
    (parentMatrixValues nodes).length=(nodes.length+1)^2 := by
  simp [parentMatrixValues]
  ring

end Counting.StackMachine.RealizabilityCheck
