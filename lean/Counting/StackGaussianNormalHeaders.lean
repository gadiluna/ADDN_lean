import Counting.StackEmitNatural
import Counting.StackRoutineFixedPrefix

namespace Counting.StackMachine.GaussianNormal
open Routine
set_option backward.isDefEq.respectTransparency false

def matrixHeaderRoles : PowerWorkspace 48 := ⟨![44,50,2,3,52],by decide⟩
def rowHeaderRoles : PowerWorkspace 48 := ⟨![44,49,2,3,52],by decide⟩
abbrev emitHeaders : Routine 51 := sequence (emitNatural 48 matrixHeaderRoles)
  (sequence (pushBit 44 true) (sequence (emitNatural 48 rowHeaderRoles) (discardBit 44)))

/-- Canonical row and matrix headers are computed from the actual unary
width. Its temporary increment is restored by an executed pop. -/
theorem emitHeaders_executes (store : Fin 53 → List Bool)
    (counter : store 2=[]) (binary : store 3=[]) (scratch : store 52=[])
    (rowEmpty : store 49=[]) (matrixEmpty : store 50=[]) :
    ∃ time ≤ 50*((store 44).length+2)^2,
      Executes emitHeaders store time
        (Function.update (Function.update store 50 (Encoding.natural.encode (store 44).length))
          49 (Encoding.natural.encode ((store 44).length+1))) := by
  let matrix := Function.update store 50 (Encoding.natural.encode (store 44).length)
  let incremented := Function.update matrix 44 (true::store 44)
  let row := Function.update incremented 49 (Encoding.natural.encode ((store 44).length+1))
  obtain ⟨firstTime,firstBound,a⟩ := emitNatural_executes 48 matrixHeaderRoles store counter binary scratch
  have firstStore : Function.update store (matrixHeaderRoles 1)
      (Encoding.natural.encode (store (matrixHeaderRoles 0)).length++store (matrixHeaderRoles 1))=matrix := by
    simp [matrixHeaderRoles,matrix,matrixEmpty]
  rw [firstStore] at a
  have b := pushBit_executes (44 : Fin 53) true matrix
  have next : Function.update matrix 44 (true::matrix 44)=incremented := by simp [matrix,incremented]
  rw [next] at b
  obtain ⟨secondTime,secondBound,c⟩ := emitNatural_executes 48 rowHeaderRoles incremented
    (by simp [incremented,matrix,rowHeaderRoles,counter])
    (by simp [incremented,matrix,rowHeaderRoles,binary])
    (by simp [incremented,matrix,rowHeaderRoles,scratch])
  have secondStore : Function.update incremented (rowHeaderRoles 1)
      (Encoding.natural.encode (incremented (rowHeaderRoles 0)).length++incremented (rowHeaderRoles 1))=row := by
    simp [rowHeaderRoles,incremented,matrix,row,rowEmpty]
  rw [secondStore] at c
  have d := discardBit_executes (44 : Fin 53) row
  have restored : Function.update row 44 (row 44).tail=
      Function.update matrix 49 (Encoding.natural.encode ((store 44).length+1)) := by
    funext r;fin_cases r <;> simp [row,incremented,matrix]
  rw [restored] at d
  refine ⟨_,?_,a.sequence (b.sequence (c.sequence d))⟩
  change firstTime ≤ 20*((store 44).length+1)^2 at firstBound
  change secondTime ≤ 20*((true::store 44).length+1)^2 at secondBound
  simp only [List.length_cons] at secondBound
  have mono := Nat.pow_le_pow_left (show (store 44).length+1≤(store 44).length+2 by omega) 2
  have same : ((store 44).length+1+1)^2=((store 44).length+2)^2 := by congr 1
  rw [same] at secondBound
  have positive : 1≤((store 44).length+2)^2 := Nat.one_le_pow 2 _ (by omega)
  omega

end Counting.StackMachine.GaussianNormal
