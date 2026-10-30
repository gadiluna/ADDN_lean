import Counting.StackAnchorMatrixLeaderPrepare
import Counting.StackAnchorMatrixWidth

namespace Counting.StackMachine.AnchorMatrix
open Routine
set_option backward.isDefEq.respectTransparency false

abbrev leaderComplete : Routine 48 := sequence leaderPrepare (sequence measureWidth emit)

def leaderBudget (nodes : List Executable.Node) (anchor leaders : Nat)
    (tail query suffix : List Bool) : Nat :=
  AnchorLeaderRow.rowBudget nodes leaders anchor (Encoding.sequence Encoding.node nodes++suffix).length+
    tail.length+query.length+5*(Encoding.sequence Encoding.node nodes++suffix).length+5*leaders.size+5*nodes.length+
    suffix.length+15+1+
    (2000*((Encoding.rationalRow.encode (AnchorCoefficient.leaderRow nodes anchor leaders)).length+1)^3+1+
      (9*(Encoding.rationalRow.encode (AnchorCoefficient.leaderRow nodes anchor leaders)).length+10))

theorem leaderComplete_executes (nodes : List Executable.Node) (anchor leaders : Nat)
    (tail query suffix previous matrix rows : List Bool) :
    ∃ time ≤ leaderBudget nodes anchor leaders tail query suffix,
      Executes leaderComplete
        (bank (AnchorRow.file tail query anchor.bits [] [] [] [] [] [])
          (Encoding.sequence Encoding.node nodes++suffix) previous [] (List.replicate nodes.length true) matrix rows [] leaders.bits)
        time
        (Function.update
          (bank (AnchorRow.file [] [] anchor.bits [] [] [] [] [] [])
            (Encoding.sequence Encoding.node nodes++suffix) previous [] (List.replicate nodes.length true)
            ((Encoding.frame (Encoding.rationalRow.encode (AnchorCoefficient.leaderRow nodes anchor leaders))).reverse++matrix)
            (true::rows) [] leaders.bits)
          42 (List.replicate (AnchorCoefficient.selectedNodes nodes anchor).length true)) := by
  obtain ⟨rowTime,rowBound,a⟩ := leaderPrepare_executes nodes anchor leaders tail query suffix previous matrix rows
  let result := Encoding.rationalRow.encode (AnchorCoefficient.leaderRow nodes anchor leaders)
  let prepared := bank (AnchorRow.file [] [] anchor.bits result [] [] [] [] [])
    (Encoding.sequence Encoding.node nodes++suffix) previous [] (List.replicate nodes.length true) matrix rows [] leaders.bits
  let coefficients := (AnchorCoefficient.selectedNodes nodes anchor).map (fun node=>if node.leader then (1:Rat) else 0)
  obtain ⟨widthTime,widthBound,b⟩ := measureWidth_executes prepared coefficients (leaders:Rat) rfl rfl rfl rfl
    (by intro i member;fin_cases i <;> simp_all [prepared,bank,AnchorRow.file,widthRoles])
  let measured := Function.update prepared 42 (List.replicate coefficients.length true)
  change Executes _ prepared widthTime measured at b
  have c := emit_executes measured rfl rfl
  have cs : Function.update (Function.update (Function.update measured 22 []) 46
      ((Encoding.frame (measured 22)).reverse++measured 46)) 47 (true::measured 47)=
      Function.update
        (bank (AnchorRow.file [] [] anchor.bits [] [] [] [] [] [])
          (Encoding.sequence Encoding.node nodes++suffix) previous [] (List.replicate nodes.length true)
          ((Encoding.frame result).reverse++matrix) (true::rows) [] leaders.bits)
        42 (List.replicate (AnchorCoefficient.selectedNodes nodes anchor).length true) := by
    funext r;fin_cases r <;> simp [measured,prepared,bank,AnchorRow.file,coefficients]
  rw [cs] at c
  change Executes _ measured (9*result.length+10) _ at c
  have composed := a.sequence (b.sequence c)
  refine ⟨_,?_,composed⟩
  change widthTime ≤ 2000*(result.length+1)^3 at widthBound
  unfold leaderBudget
  dsimp only [result] at widthBound ⊢
  omega

end Counting.StackMachine.AnchorMatrix
