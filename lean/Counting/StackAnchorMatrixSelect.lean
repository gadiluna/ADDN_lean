import Counting.StackAnchorMatrixFlow

namespace Counting.StackMachine.AnchorMatrix
open Routine EncodingPrograms
set_option backward.isDefEq.respectTransparency false

def oldEqualityRoles : Fin 6 ↪ Fin 50 := ⟨![23,41,32,1,2,3],by decide⟩
abbrev selected : Routine 48 := sequence (clear 23) flow
abbrev dispatch : Routine 48 := sequence (Compare.preservingEquality 44 oldEqualityRoles)
  (branchRoutine 32 selected (clear 23))

def flowBudget (nodes : List Executable.Node) (query anchor : Nat) (tail suffix : List Bool) : Nat :=
  AnchorRow.rowBudget nodes query anchor (Encoding.sequence Encoding.node nodes++suffix).length+
    12*tail.length+5*(Encoding.sequence Encoding.node nodes++suffix).length+5*nodes.length+
    suffix.length+9*(Encoding.rationalRow.encode (AnchorCoefficient.flowRow nodes anchor query)).length+29

theorem selected_executes (nodes : List Executable.Node) (query anchor level previous : Nat)
    (tail suffix matrix rows outer leaders : List Bool) :
    ∃ time ≤ level.size+2+flowBudget nodes query anchor tail suffix,
      Executes selected
        (bank (AnchorRow.file tail query.bits anchor.bits [] level.bits [] [] [] [])
          (Encoding.sequence Encoding.node nodes++suffix) previous.bits [] (List.replicate nodes.length true) matrix rows outer leaders)
        time
        (bank (AnchorRow.file tail query.bits anchor.bits [] [] [] [] [] [])
          (Encoding.sequence Encoding.node nodes++suffix) previous.bits [] (List.replicate nodes.length true)
          ((Encoding.frame (Encoding.rationalRow.encode (AnchorCoefficient.flowRow nodes anchor query))).reverse++matrix)
          (true::rows) outer leaders) := by
  let table := Encoding.sequence Encoding.node nodes++suffix
  let before := bank (AnchorRow.file tail query.bits anchor.bits [] level.bits [] [] [] [])
    table previous.bits [] (List.replicate nodes.length true) matrix rows outer leaders
  have a := clear_executes (23:Fin 50) before
  have as' : Function.update before 23 []=
      bank (AnchorRow.file tail query.bits anchor.bits [] [] [] [] [] [])
        table previous.bits [] (List.replicate nodes.length true) matrix rows outer leaders := by
    funext r;fin_cases r <;> simp [before,bank,AnchorRow.file]
  rw [as'] at a
  change Executes _ before (level.bits.length+1) _ at a
  rw [Encoding.bits_length] at a
  obtain ⟨time,bounded,ran⟩ := flow_executes nodes query anchor tail suffix previous.bits matrix rows outer leaders
  refine ⟨level.size+1+1+time,by dsimp only [flowBudget];omega,a.sequence ran⟩

/-- Selecting an old-level node invokes the complete physical row builder;
other levels only clear the temporary label. The matrix stream and its
unary row count are changed exactly in the selected branch. -/
theorem dispatch_executes (nodes : List Executable.Node) (query anchor level previous : Nat)
    (tail suffix matrix rows outer leaders : List Bool) :
    ∃ time ≤ 7*level.size+6*previous.size+20+flowBudget nodes query anchor tail suffix,
      Executes dispatch
        (bank (AnchorRow.file tail query.bits anchor.bits [] level.bits [] [] [] [])
          (Encoding.sequence Encoding.node nodes++suffix) previous.bits [] (List.replicate nodes.length true) matrix rows outer leaders)
        time
        (bank (AnchorRow.file tail query.bits anchor.bits [] [] [] [] [] [])
          (Encoding.sequence Encoding.node nodes++suffix) previous.bits [] (List.replicate nodes.length true)
          (if level=previous then
            (Encoding.frame (Encoding.rationalRow.encode (AnchorCoefficient.flowRow nodes anchor query))).reverse++matrix else matrix)
          (if level=previous then true::rows else rows) outer leaders) := by
  let table := Encoding.sequence Encoding.node nodes++suffix
  let before := bank (AnchorRow.file tail query.bits anchor.bits [] level.bits [] [] [] [])
    table previous.bits [] (List.replicate nodes.length true) matrix rows outer leaders
  have a := Compare.preservingEquality_executes 44 oldEqualityRoles before rfl rfl rfl
  change Executes _ before (Compare.preservingCost level.bits previous.bits)
    (Function.update before 32 [decide (level.bits=previous.bits)]) at a
  have cost := Compare.preservingCost_le level.bits previous.bits
  simp only [Encoding.bits_length] at cost
  have reset (bit : Bool) : Function.update (Function.update before 32 [bit]) 32 []=before := by
    rw [Function.update_idem]
    have empty : before 32=[] := rfl
    rw [←empty,Function.update_eq_self]
  by_cases equal : level=previous
  · have truth : decide (level.bits=previous.bits)=true := by simp [equal]
    rw [truth] at a
    obtain ⟨time,bounded,ran⟩ := selected_executes nodes query anchor level previous tail suffix matrix rows outer leaders
    have b := branch_executes_true (32:Fin 50) selected (clear 23)
      (Function.update before 32 [true]) _ [] time (by simp)
      (by rw [reset];exact ran)
    have composed := a.sequence b
    refine ⟨Compare.preservingCost level.bits previous.bits+1+(1+time),by omega,?_⟩
    simpa only [dispatch,if_pos equal] using composed
  · have falsity : decide (level.bits=previous.bits)=false := by simp [Encoding.bits_injective.eq_iff,equal]
    rw [falsity] at a
    have cleared := clear_executes (23:Fin 50) before
    have clearedStore : Function.update before 23 []=
        bank (AnchorRow.file tail query.bits anchor.bits [] [] [] [] [] [])
          table previous.bits [] (List.replicate nodes.length true) matrix rows outer leaders := by
      funext r;fin_cases r <;> simp [before,bank,AnchorRow.file]
    rw [clearedStore] at cleared
    change Executes _ before (level.bits.length+1) _ at cleared
    rw [Encoding.bits_length] at cleared
    have b := branch_executes_false (32:Fin 50) selected (clear 23)
      (Function.update before 32 [false]) _ [] _ (by simp) (by rw [reset];exact cleared)
    have composed := a.sequence b
    refine ⟨Compare.preservingCost level.bits previous.bits+1+(1+(level.size+1)),by omega,?_⟩
    simpa only [dispatch,if_neg equal] using composed

end Counting.StackMachine.AnchorMatrix
