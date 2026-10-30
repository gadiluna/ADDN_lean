import Counting.StackAnchorMatrixLoop
import Counting.StackAnchorMatrixLeaderComplete
import Counting.StackAnchorMatrixFinish
import Counting.AnchorMatrixOrder

namespace Counting.StackMachine.AnchorMatrix
open Routine
set_option backward.isDefEq.respectTransparency false

def producedRows (nodes : List Executable.Node) (anchor previous leaders : Nat) : List (List Rat) :=
  generatedRows nodes anchor previous 0 nodes++[AnchorCoefficient.leaderRow nodes anchor leaders]

abbrev buildRows : Routine 48 := sequence loop (sequence leaderComplete finish)

def buildBudget (nodes : List Executable.Node) (anchor previous leaders : Nat) (suffix : List Bool) : Nat :=
  let rows := producedRows nodes anchor previous leaders
  loopBudget nodes anchor previous suffix 0 nodes+1+
    (leaderBudget nodes anchor leaders suffix nodes.length.bits suffix+1+
      (4*rows.length*(rows.length+1)+17*rows.length+
        2*(Encoding.sequence (Encoding.framed Encoding.rationalRow) rows).length+20))

/-- Construct every flow equation in stored-node order, append normalization,
and materialize the matrix header. The unary column count is retained in 42. -/
theorem buildRows_executes (nodes : List Executable.Node) (anchor previous leaders : Nat) (suffix : List Bool) :
    ∃ time ≤ buildBudget nodes anchor previous leaders suffix,
      Executes buildRows
        (bank (AnchorRow.file (Encoding.sequence Encoding.node nodes++suffix) [] anchor.bits [] [] [] [] [] [])
          (Encoding.sequence Encoding.node nodes++suffix) previous.bits [] (List.replicate nodes.length true)
          [] [] (List.replicate nodes.length true) leaders.bits) time
        (Function.update
          (bank (AnchorRow.file [] [] anchor.bits (Encoding.rationalMatrix.encode (producedRows nodes anchor previous leaders))
              [] [] [] [] [])
            (Encoding.sequence Encoding.node nodes++suffix) previous.bits [] (List.replicate nodes.length true)
            [] [] [] leaders.bits)
          42 (List.replicate (AnchorCoefficient.selectedNodes nodes anchor).length true)) := by
  obtain ⟨loopTime,loopBound,a⟩ := loop_executes nodes nodes 0 anchor previous suffix [] [] leaders.bits
  simp only [Nat.zero_add,List.append_nil] at a
  let flowRows := generatedRows nodes anchor previous 0 nodes
  let matrix := (Encoding.sequence (Encoding.framed Encoding.rationalRow) flowRows).reverse
  obtain ⟨leaderTime,leaderBound,b⟩ := leaderComplete_executes nodes anchor leaders suffix nodes.length.bits suffix
    previous.bits matrix (List.replicate flowRows.length true)
  let rows := producedRows nodes anchor previous leaders
  let finished := Function.update
    (bank (AnchorRow.file [] [] anchor.bits [] [] [] [] [] [])
      (Encoding.sequence Encoding.node nodes++suffix) previous.bits [] (List.replicate nodes.length true)
      (Encoding.sequence (Encoding.framed Encoding.rationalRow) rows).reverse
      (List.replicate rows.length true) [] leaders.bits)
    42 (List.replicate (AnchorCoefficient.selectedNodes nodes anchor).length true)
  have appended : Encoding.sequence (Encoding.framed Encoding.rationalRow) rows=
      Encoding.sequence (Encoding.framed Encoding.rationalRow) flowRows++
        Encoding.frame (Encoding.rationalRow.encode (AnchorCoefficient.leaderRow nodes anchor leaders)) := by
    change Encoding.sequence (Encoding.framed Encoding.rationalRow)
      (flowRows++[AnchorCoefficient.leaderRow nodes anchor leaders])=_
    induction flowRows with
    | nil => simp [Encoding.sequence,Encoding.framed]
    | cons row rest ih => simp only [List.cons_append,Encoding.sequence,ih,List.append_assoc]
  have bs : Function.update
      (bank (AnchorRow.file [] [] anchor.bits [] [] [] [] [] [])
        (Encoding.sequence Encoding.node nodes++suffix) previous.bits [] (List.replicate nodes.length true)
        ((Encoding.frame (Encoding.rationalRow.encode (AnchorCoefficient.leaderRow nodes anchor leaders))).reverse++matrix)
        (true::List.replicate flowRows.length true) [] leaders.bits)
      42 (List.replicate (AnchorCoefficient.selectedNodes nodes anchor).length true)=finished := by
    have count : rows.length=flowRows.length+1 := by simp [rows,producedRows,flowRows]
    simp only [finished,appended,List.reverse_append,count,List.replicate_succ,matrix]
  rw [bs] at b
  obtain ⟨finishTime,finishBound,c⟩ := finish_executes finished rows rfl rfl rfl rfl
    (by simp [finished,bank])
  have cs : Function.update (Function.update (Function.update finished 47 []) 46 []) 22
      (Encoding.rationalMatrix.encode rows)=
      Function.update
        (bank (AnchorRow.file [] [] anchor.bits (Encoding.rationalMatrix.encode rows) [] [] [] [] [])
          (Encoding.sequence Encoding.node nodes++suffix) previous.bits [] (List.replicate nodes.length true)
          [] [] [] leaders.bits)
        42 (List.replicate (AnchorCoefficient.selectedNodes nodes anchor).length true) := by
    funext r;fin_cases r <;> simp [finished,bank,AnchorRow.file]
  rw [cs] at c
  have composed := a.sequence (b.sequence c)
  refine ⟨_,?_,composed⟩
  dsimp only [buildBudget]
  dsimp only [rows] at finishBound
  omega

theorem producedRows_vista (vista : Executable.Vista) (anchor leaders : Nat) :
    producedRows vista.nodes.toList anchor (anchor-1) leaders=AnchorCoefficient.matrix vista anchor leaders := by
  unfold producedRows AnchorCoefficient.matrix
  rw [generatedRows_all]

end Counting.StackMachine.AnchorMatrix
