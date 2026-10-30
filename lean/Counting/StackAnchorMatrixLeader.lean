import Counting.StackAnchorMatrixBank
import Counting.StackAnchorLeaderRow

namespace Counting.StackMachine.AnchorMatrix
open Routine EncodingPrograms
set_option backward.isDefEq.respectTransparency false

abbrev leaderPass : Routine 48 := sequence (clear 0) (sequence (clear 21)
  (sequence (ofProgram (ListPrograms.copyProgram 47 40 0 39))
    (sequence (ofProgram (ListPrograms.copyProgram 47 49 21 39))
      (sequence (ofProgram (ListPrograms.copyProgram 47 45 37 39))
        (sequence (relocate AnchorLeaderRow.row rowRoles) (sequence (clear 0) emit))))))

theorem leaderPass_executes (nodes : List Executable.Node) (anchor leaders : Nat)
    (tail query suffix previous matrix rows : List Bool) :
    ∃ time ≤ AnchorLeaderRow.rowBudget nodes leaders anchor (Encoding.sequence Encoding.node nodes++suffix).length+
        tail.length+query.length+5*(Encoding.sequence Encoding.node nodes++suffix).length+5*leaders.size+5*nodes.length+
        suffix.length+9*(Encoding.rationalRow.encode (AnchorCoefficient.leaderRow nodes anchor leaders)).length+26,
      Executes leaderPass
        (bank (AnchorRow.file tail query anchor.bits [] [] [] [] [] [])
          (Encoding.sequence Encoding.node nodes++suffix) previous [] (List.replicate nodes.length true) matrix rows [] leaders.bits)
        time
        (bank (AnchorRow.file [] [] anchor.bits [] [] [] [] [] [])
          (Encoding.sequence Encoding.node nodes++suffix) previous [] (List.replicate nodes.length true)
          ((Encoding.frame (Encoding.rationalRow.encode (AnchorCoefficient.leaderRow nodes anchor leaders))).reverse++matrix)
          (true::rows) [] leaders.bits) := by
  let table := Encoding.sequence Encoding.node nodes++suffix
  let count := List.replicate nodes.length true
  let inner (input query output counter : List Bool) := AnchorRow.file input query anchor.bits output [] [] [] counter []
  let start := bank (inner tail query [] []) table previous [] count matrix rows [] leaders.bits
  let cleared := bank (inner [] query [] []) table previous [] count matrix rows [] leaders.bits
  have a := clear_executes (0:Fin 50) start
  have as' : Function.update start 0 []=cleared := by funext r;fin_cases r <;> simp [start,cleared,inner,bank,AnchorRow.file]
  rw [as'] at a
  change Executes _ start (tail.length+1) cleared at a
  let ready := bank (inner [] [] [] []) table previous [] count matrix rows [] leaders.bits
  have b := clear_executes (21:Fin 50) cleared
  have bs : Function.update cleared 21 []=ready := by funext r;fin_cases r <;> simp [cleared,ready,inner,bank,AnchorRow.file]
  rw [bs] at b
  change Executes _ cleared (query.length+1) ready at b
  let copied := bank (inner table [] [] []) table previous [] count matrix rows [] leaders.bits
  have c := copy_executes 47 (40:Fin 50) 0 39 (by decide) (by decide) (by decide) ready rfl
  have cs : Function.update ready 0 (ready 40++ready 0)=copied := by
    funext r;fin_cases r <;> simp [ready,copied,inner,bank,AnchorRow.file]
  rw [cs] at c
  change Executes _ ready (5*table.length+2) copied at c
  let parameterized := bank (inner table leaders.bits [] []) table previous [] count matrix rows [] leaders.bits
  have d := copy_executes 47 (49:Fin 50) 21 39 (by decide) (by decide) (by decide) copied rfl
  have ds : Function.update copied 21 (copied 49++copied 21)=parameterized := by
    funext r;fin_cases r <;> simp [copied,parameterized,inner,bank,AnchorRow.file]
  rw [ds] at d
  change Executes _ copied (5*leaders.bits.length+2) parameterized at d
  rw [Encoding.bits_length] at d
  let counted := bank (inner table leaders.bits [] count) table previous [] count matrix rows [] leaders.bits
  have e := copy_executes 47 (45:Fin 50) 37 39 (by decide) (by decide) (by decide) parameterized rfl
  have es : Function.update parameterized 37 (parameterized 45++parameterized 37)=counted := by
    funext r;fin_cases r <;> simp [parameterized,counted,inner,bank,AnchorRow.file]
  rw [es] at e
  change Executes _ parameterized (5*count.length+2) counted at e
  simp only [count,List.length_replicate] at e
  obtain ⟨rowTime,rowBound,rowRun⟩ := AnchorLeaderRow.row_executes nodes leaders anchor suffix table.length (by rfl)
  let result := Encoding.rationalRow.encode (AnchorCoefficient.leaderRow nodes anchor leaders)
  let built := bank (inner suffix [] result []) table previous [] count matrix rows [] leaders.bits
  have f : Executes (relocate AnchorLeaderRow.row rowRoles) counted rowTime built :=
    lift_executes AnchorLeaderRow.row _ _ rowTime table previous [] count matrix rows [] leaders.bits rowRun
  have g := clear_executes (0:Fin 50) built
  let erased := bank (inner [] [] result []) table previous [] count matrix rows [] leaders.bits
  have gs : Function.update built 0 []=erased := by
    funext r;fin_cases r <;> simp [built,erased,inner,bank,AnchorRow.file]
  rw [gs] at g
  change Executes _ built (suffix.length+1) erased at g
  have h := emit_executes erased rfl rfl
  let final := bank (inner [] [] [] []) table previous [] count
    ((Encoding.frame result).reverse++matrix) (true::rows) [] leaders.bits
  have hs : Function.update (Function.update (Function.update erased 22 []) 46
      ((Encoding.frame (erased 22)).reverse++erased 46)) 47 (true::erased 47)=final := by
    funext r;fin_cases r <;> simp [erased,final,inner,bank,AnchorRow.file]
  rw [hs] at h
  change Executes _ erased (9*result.length+10) final at h
  have composed := a.sequence (b.sequence (c.sequence (d.sequence (e.sequence (f.sequence (g.sequence h))))))
  refine ⟨_,?_,composed⟩
  dsimp only [table,result] at rowBound ⊢
  omega

end Counting.StackMachine.AnchorMatrix
