import Counting.StackFramedList
import Counting.StackPositiveNaturalsCall
import Counting.StackRationalPredicateSpec
import Counting.StackRowScaleBounds

namespace Counting.StackMachine.GaussianCoefficient
open Routine

def file (row index payload present zero : List Bool) : Fin 26 → List Bool :=
  ![row,index,payload,present,zero,[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]]
def readRoles : Fin 8 ↪ Fin 26 := ⟨![0,1,2,3,5,6,7,8],by decide⟩
def zeroRoles : Fin 20 ↪ Fin 26 := ⟨![2,4,5,6,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25],by decide⟩
abbrev readCoefficient : Routine 24 := FieldAccess.preservingRead 18 readRoles
abbrev testZero : Routine 24 := relocate
  (PositiveNaturalsCall.invoke (RationalArithmetic.Predicates.routine .zero)) zeroRoles
abbrev inspect : Routine 24 := sequence readCoefficient testZero

/-- The index is explicitly unary and includes the list-header field. Both
source row and index are retained; the returned payload is the exact scalar codec. -/
theorem readCoefficient_executes (row : List Rat) (index : Nat) (value : Rat)
    (selected : row[index]?=some value) :
    ∃ time ≤ 10*(Encoding.rationalRow.encode row).length+8*(index+1)+14,
      Executes readCoefficient (file (Encoding.rationalRow.encode row) (List.replicate (index+1) true) [] [] []) time
        (file (Encoding.rationalRow.encode row) (List.replicate (index+1) true) (Encoding.rational.encode value) [true] []) := by
  let store := file (Encoding.rationalRow.encode row) (List.replicate (index+1) true) [] [] []
  obtain ⟨time,bounded,ran⟩ := FieldAccess.preservingRead_executes 18 readRoles store rfl rfl rfl rfl
  have selection : FieldAccess.selectPayload (Encoding.rationalRow.encode row) (index+1)=some (Encoding.rational.encode value) := by
    rw [Encoding.rationalRow,FieldAccess.selectPayload_framedList Encoding.rational row index,selected]
    rfl
  have result : Function.update (Function.update store (readRoles 2)
      ((FieldAccess.selectPayload (store (readRoles 0)) (store (readRoles 1)).length).getD []++store (readRoles 2)))
      (readRoles 3) ((FieldAccess.selectPayload (store (readRoles 0)) (store (readRoles 1)).length).isSome::store (readRoles 3)) =
      file (Encoding.rationalRow.encode row) (List.replicate (index+1) true) (Encoding.rational.encode value) [true] [] := by
    funext r; fin_cases r <;> simp [store,file,readRoles,selection]
  rw [result] at ran
  refine ⟨time,?_,ran⟩
  simpa [store,file,readRoles] using bounded

theorem testZero_executes (row index : List Bool) (value : Rat) :
    ∃ time ≤ 2000*((Encoding.rational.encode value).length+1),
      Executes testZero (file row index (Encoding.rational.encode value) [true] []) time
        (file row index (Encoding.rational.encode value) [true] [decide (value=0)]) := by
  obtain ⟨time,bounded,ran⟩ := PositiveNaturalsCall.invoke_executes
    (RationalArithmetic.Predicates.routine .zero) _ _
    (RationalArithmetic.Predicates.predicate_computes .zero) (Encoding.rational.encode value)
  change Executes _ _ time (PositiveNaturalsCall.file (Encoding.rational.encode value)
    [RationalArithmetic.Predicates.predicate .zero (Encoding.rational.encode value)] [] []) at ran
  rw [RationalArithmetic.Predicates.zero_correct] at ran
  refine ⟨time,?_,?_⟩
  · simp only [Complexity.polynomial,pow_one] at bounded
    omega
  · apply relocate_executes_frame
      (PositiveNaturalsCall.invoke (RationalArithmetic.Predicates.routine .zero)) zeroRoles _ _ _ _ time _ _ _ ran
    · funext r; fin_cases r <;> simp [file,PositiveNaturalsCall.file,zeroRoles]
    · intro r; fin_cases r <;> simp [file,PositiveNaturalsCall.file,zeroRoles]
    · intro r outside
      fin_cases r
      · simp [file]
      · simp [file]
      · simp [file]
      · simp [file]
      · exact False.elim (outside 1 rfl)
      all_goals simp [file]

/-- An actual frame lookup followed by the actual scalar zero tester.
The bound includes reading the unary index; its construction is not free. -/
theorem inspect_executes (row : List Rat) (index : Nat) (value : Rat)
    (selected : row[index]?=some value) :
    ∃ time ≤ 3000*((Encoding.rationalRow.encode row).length+index+2),
      Executes inspect (file (Encoding.rationalRow.encode row) (List.replicate (index+1) true) [] [] []) time
        (file (Encoding.rationalRow.encode row) (List.replicate (index+1) true)
          (Encoding.rational.encode value) [true] [decide (value=0)]) := by
  obtain ⟨readTime,readBound,readRun⟩ := readCoefficient_executes row index value selected
  obtain ⟨testTime,testBound,testRun⟩ := testZero_executes (Encoding.rationalRow.encode row) (List.replicate (index+1) true) value
  have size := RowScale.member_row_length_le row value (List.mem_of_getElem? selected)
  exact ⟨_,by omega,readRun.sequence testRun⟩

end Counting.StackMachine.GaussianCoefficient
