import Counting.StackAnchorMatrixSelect

namespace Counting.StackMachine.AnchorMatrix
open Routine EncodingPrograms
set_option backward.isDefEq.respectTransparency false

abbrev advanceIndex : Routine 48 := DagValidation.incrementRoutine 47 38 21 39
abbrev item : Routine 48 := sequence (relocate AnchorRow.calculate rowRoles)
  (sequence (clear 22) (sequence dispatch advanceIndex))

def stepBudget (nodes : List Executable.Node) (node : Executable.Node) (query anchor previous : Nat)
    (tail suffix : List Bool) : Nat :=
  100000*((Encoding.node.encode node++tail).length+query.size+1)^3+
    (AnchorRow.word node query).length+7*node.level.size+6*previous.size+
    flowBudget nodes query anchor tail suffix+4*query.size+31

theorem item_executes (nodes : List Executable.Node) (node : Executable.Node) (query anchor previous : Nat)
    (tail suffix matrix rows outer leaders : List Bool) :
    ∃ time ≤ stepBudget nodes node query anchor previous tail suffix,
      Executes item
        (bank (AnchorRow.file (Encoding.node.encode node++tail) query.bits anchor.bits [] [] [] [] [] [])
          (Encoding.sequence Encoding.node nodes++suffix) previous.bits [] (List.replicate nodes.length true) matrix rows outer leaders)
        time
        (bank (AnchorRow.file tail (query+1).bits anchor.bits [] [] [] [] [] [])
          (Encoding.sequence Encoding.node nodes++suffix) previous.bits [] (List.replicate nodes.length true)
          (if node.level=previous then
            (Encoding.frame (Encoding.rationalRow.encode (AnchorCoefficient.flowRow nodes anchor query))).reverse++matrix else matrix)
          (if node.level=previous then true::rows else rows) outer leaders) := by
  let table := Encoding.sequence Encoding.node nodes++suffix
  let count := List.replicate nodes.length true
  obtain ⟨readTime,readBound,readRun⟩ := AnchorRow.calculate_executes node query tail anchor.bits [] [] []
  have a := lift_executes AnchorRow.calculate _ _ readTime table previous.bits [] count matrix rows outer leaders readRun
  let read := bank (AnchorRow.file tail query.bits anchor.bits (AnchorRow.word node query) node.level.bits [] [] [] [])
    table previous.bits [] count matrix rows outer leaders
  let clean := bank (AnchorRow.file tail query.bits anchor.bits [] node.level.bits [] [] [] [])
    table previous.bits [] count matrix rows outer leaders
  have b := clear_executes (22:Fin 50) read
  have bs : Function.update read 22 []=clean := by
    funext r;fin_cases r <;> simp [read,clean,bank,AnchorRow.file]
  rw [bs] at b
  change Executes _ read ((AnchorRow.word node query).length+1) clean at b
  obtain ⟨dispatchTime,dispatchBound,c⟩ := dispatch_executes nodes query anchor node.level previous tail suffix matrix rows outer leaders
  let nextMatrix := if node.level=previous then
    (Encoding.frame (Encoding.rationalRow.encode (AnchorCoefficient.flowRow nodes anchor query))).reverse++matrix else matrix
  let nextCount := if node.level=previous then true::rows else rows
  let selectedStore := bank (AnchorRow.file tail query.bits anchor.bits [] [] [] [] [] [])
    table previous.bits [] count nextMatrix nextCount outer leaders
  obtain ⟨incrementTime,incrementBound,d⟩ := DagValidation.increment_natural 47 (38:Fin 50) 21 39
    (by decide) (by decide) (by decide) selectedStore rfl rfl query rfl
  have ds : Function.update selectedStore 21 (query+1).bits=
      bank (AnchorRow.file tail (query+1).bits anchor.bits [] [] [] [] [] [])
        table previous.bits [] count nextMatrix nextCount outer leaders := by
    funext r;fin_cases r <;> simp [selectedStore,bank,AnchorRow.file]
  rw [ds] at d
  have composed := a.sequence (b.sequence (c.sequence d))
  refine ⟨readTime+1+((AnchorRow.word node query).length+1+1+(dispatchTime+1+incrementTime)),?_,composed⟩
  unfold stepBudget
  omega

end Counting.StackMachine.AnchorMatrix
