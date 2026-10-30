import Counting.StackAnchorMatrixBank

namespace Counting.StackMachine.AnchorMatrix
open Routine
set_option backward.isDefEq.respectTransparency false

def finishRoles : Fin 40 ↪ Fin 50 :=
  ⟨fun r=>if r=35 then 46 else if r=36 then 47 else ⟨r.val,by have:=r.isLt;omega⟩,by decide⟩

abbrev finish : Routine 48 := relocate AnchorRow.finish finishRoles

/-- Finish the matrix list using the actual row counter and emitted row fields. -/
theorem finish_executes (store : Store 48) (rows : List (List Rat))
    (outputEmpty : store 22=[]) (binaryEmpty : store 38=[]) (scratchEmpty : store 39=[])
    (reversed : store 46=(Encoding.sequence (Encoding.framed Encoding.rationalRow) rows).reverse)
    (count : (store 47).length=rows.length) :
    ∃ time ≤ 4*rows.length*(rows.length+1)+17*rows.length+
        2*(Encoding.sequence (Encoding.framed Encoding.rationalRow) rows).length+20,
      Executes finish store time
        (Function.update (Function.update (Function.update store 47 []) 46 []) 22
          (Encoding.rationalMatrix.encode rows)) := by
  let localStore := store ∘ finishRoles
  obtain ⟨time,bounded,ran⟩ := AnchorRow.finish_executes localStore
    (Encoding.sequence (Encoding.framed Encoding.rationalRow) rows)
    outputEmpty binaryEmpty scratchEmpty reversed
  let after := Function.update (Function.update (Function.update store 47 []) 46 []) 22
    (Encoding.rationalMatrix.encode rows)
  have lifted : Executes finish store time after := by
    apply relocate_executes_frame AnchorRow.finish finishRoles store after localStore _ time rfl _ _ ran
    · intro r
      fin_cases r <;> simp [after,localStore,finishRoles,Function.comp_def,count,Encoding.rationalMatrix,Encoding.list]
    · intro r outside
      have r22 := outside 22
      have r46 := outside 35
      have r47 := outside 36
      change (22:Fin 50) ≠ r at r22
      change (46:Fin 50) ≠ r at r46
      change (47:Fin 50) ≠ r at r47
      simp [after,r22.symm,r46.symm,r47.symm]
  refine ⟨time,?_,lifted⟩
  change time ≤ 4*(store 47).length*((store 47).length+1)+17*(store 47).length+
    2*(Encoding.sequence (Encoding.framed Encoding.rationalRow) rows).length+20 at bounded
  simpa only [count] using bounded

end Counting.StackMachine.AnchorMatrix
