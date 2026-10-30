import Counting.StackAnchorMatrixBank

namespace Counting.StackMachine.AnchorMatrix
open Routine EncodingPrograms
set_option backward.isDefEq.respectTransparency false

theorem flow_executes (nodes : List Executable.Node) (query anchor : Nat)
    (tail suffix previous matrix rows outer leaders : List Bool) :
    ∃ time ≤ AnchorRow.rowBudget nodes query anchor (Encoding.sequence Encoding.node nodes++suffix).length+
        12*tail.length+5*(Encoding.sequence Encoding.node nodes++suffix).length+5*nodes.length+
        suffix.length+9*(Encoding.rationalRow.encode (AnchorCoefficient.flowRow nodes anchor query)).length+29,
      Executes flow
        (bank (AnchorRow.file tail query.bits anchor.bits [] [] [] [] [] [])
          (Encoding.sequence Encoding.node nodes++suffix) previous [] (List.replicate nodes.length true) matrix rows outer leaders)
        time
        (bank (AnchorRow.file tail query.bits anchor.bits [] [] [] [] [] [])
          (Encoding.sequence Encoding.node nodes++suffix) previous [] (List.replicate nodes.length true)
          ((Encoding.frame (Encoding.rationalRow.encode (AnchorCoefficient.flowRow nodes anchor query))).reverse++matrix)
          (true::rows) outer leaders) := by
  let table := Encoding.sequence Encoding.node nodes++suffix
  let count := List.replicate nodes.length true
  let inner (input output counter : List Bool) := AnchorRow.file input query.bits anchor.bits output [] [] [] counter []
  let start := bank (inner tail [] []) table previous [] count matrix rows outer leaders
  let saved := bank (inner [] [] []) table previous tail count matrix rows outer leaders
  have a := move_executes 47 (0:Fin 50) 44 39 (by decide) (by decide) (by decide) start rfl
  have as' : Function.update (Function.update start 44 (start 0++start 44)) 0 []=saved := by
    funext r;fin_cases r <;> simp [start,saved,inner,bank,AnchorRow.file]
  rw [as'] at a
  change Executes _ start (6*tail.length+4) saved at a
  let copied := bank (inner table [] []) table previous tail count matrix rows outer leaders
  have b := copy_executes 47 (40:Fin 50) 0 39 (by decide) (by decide) (by decide) saved rfl
  have bs : Function.update saved 0 (saved 40++saved 0)=copied := by
    funext r;fin_cases r <;> simp [saved,copied,inner,bank,AnchorRow.file]
  rw [bs] at b
  change Executes _ saved (5*table.length+2) copied at b
  let ready := bank (inner table [] count) table previous tail count matrix rows outer leaders
  have c := copy_executes 47 (45:Fin 50) 37 39 (by decide) (by decide) (by decide) copied rfl
  have cs : Function.update copied 37 (copied 45++copied 37)=ready := by
    funext r;fin_cases r <;> simp [copied,ready,inner,bank,AnchorRow.file]
  rw [cs] at c
  change Executes _ copied (5*count.length+2) ready at c
  simp only [count,List.length_replicate] at c
  obtain ⟨rowTime,rowBound,rowRun⟩ := AnchorRow.row_executes nodes query anchor suffix table.length (by rfl)
  let result := Encoding.rationalRow.encode (AnchorCoefficient.flowRow nodes anchor query)
  let built := bank (inner suffix result []) table previous tail count matrix rows outer leaders
  have d : Executes (relocate AnchorRow.row rowRoles) ready rowTime built :=
    lift_executes AnchorRow.row _ _ rowTime table previous tail count matrix rows outer leaders rowRun
  have e := clear_executes (0:Fin 50) built
  let erased := bank (inner [] result []) table previous tail count matrix rows outer leaders
  have es : Function.update built 0 []=erased := by
    funext r;fin_cases r <;> simp [built,erased,inner,bank,AnchorRow.file]
  rw [es] at e
  change Executes _ built (suffix.length+1) erased at e
  have f := move_executes 47 (44:Fin 50) 0 39 (by decide) (by decide) (by decide) erased rfl
  let restored := bank (inner tail result []) table previous [] count matrix rows outer leaders
  have fs : Function.update (Function.update erased 0 (erased 44++erased 0)) 44 []=restored := by
    funext r;fin_cases r <;> simp [erased,restored,inner,bank,AnchorRow.file]
  rw [fs] at f
  change Executes _ erased (6*tail.length+4) restored at f
  have g := emit_executes restored rfl rfl
  let final := bank (inner tail [] []) table previous [] count
    ((Encoding.frame result).reverse++matrix) (true::rows) outer leaders
  have gs : Function.update (Function.update (Function.update restored 22 []) 46
      ((Encoding.frame (restored 22)).reverse++restored 46)) 47 (true::restored 47)=final := by
    funext r;fin_cases r <;> simp [restored,final,inner,bank,AnchorRow.file]
  rw [gs] at g
  change Executes _ restored (9*result.length+10) final at g
  have composed := a.sequence (b.sequence (c.sequence (d.sequence (e.sequence (f.sequence g)))))
  refine ⟨_,?_,composed⟩
  dsimp only [table,result] at rowBound ⊢
  omega

end Counting.StackMachine.AnchorMatrix
