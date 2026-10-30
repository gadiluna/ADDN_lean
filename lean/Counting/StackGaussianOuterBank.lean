import Counting.StackGaussianStep
import Counting.StoredGaussianPivots

namespace Counting.StackMachine.GaussianBank
open Routine DirectedCounting.VerifiedGaussianAnchorSolver RationalSystem
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 20000

/-- The external pivot counter is separate from the row-loop counter. -/
def outerRoles : Fin 52 ↪ Fin 53 := ⟨fun r => ⟨r.val,by omega⟩,
  fun _ _ equal => Fin.ext (congrArg (fun r : Fin 53 => r.val) equal)⟩

def outerStore {q : Nat} (state : GaussianState q) (pivot : Nat) (counter : List Bool) : Fin 53 → List Bool :=
  fun r => if inside : r.val<52 then stateStore state pivot [] [] [] [] ⟨r.val,inside⟩ else counter

@[simp] theorem outerStore_at {q : Nat} (state : GaussianState q) (pivot : Nat) (counter : List Bool) (r : Fin 52) :
    outerStore state pivot counter (outerRoles r)=stateStore state pivot [] [] [] [] r := by
  simp [outerStore,outerRoles,r.isLt]

@[simp] theorem outerStore_last {q : Nat} (state : GaussianState q) (pivot : Nat) (counter : List Bool) :
    outerStore state pivot counter 52=counter := rfl

theorem outerStore_restrict {q : Nat} (state : GaussianState q) (pivot : Nat) (counter : List Bool) :
    outerStore state pivot counter ∘ outerRoles=stateStore state pivot [] [] [] [] := by
  funext r;exact outerStore_at state pivot counter r

theorem outerStore_relocate {q : Nat} (state result : GaussianState q) (pivot : Nat) (counter : List Bool) :
    relocatedStore outerRoles (outerStore state pivot counter) (stateStore result pivot [] [] [] [])=
      outerStore result pivot counter := by
  funext r
  by_cases inside : r.val<52
  · let localIndex : Fin 52 := ⟨r.val,inside⟩
    have equal : r=outerRoles localIndex := Fin.ext rfl
    rw [equal,relocatedStore_at,outerStore_at]
  · have outside : ∀ i,outerRoles i≠r := by
      intro i same
      have equal := congrArg Fin.val same
      simp only [outerRoles,Function.Embedding.coeFn_mk] at equal
      omega
    rw [relocatedStore_outside _ _ _ _ outside]
    simp [outerStore,inside]

abbrev outerPivot : Routine 51 := relocate pivotStepRoutine outerRoles

theorem outerPivot_executes {q : Nat} (state : GaussianState q) (pivot : Fin q) (counter : List Bool) :
    ∃ time ≤ pivotStepCost state pivot,
      Executes outerPivot (outerStore state pivot.val counter) time
        (outerStore (StoredGaussian.pivotStep state pivot) pivot.val counter) := by
  obtain ⟨time,bounded,ran⟩ := pivotStep_executes state pivot
  have localRun : Executes pivotStepRoutine (outerStore state pivot.val counter ∘ outerRoles) time
      (stateStore (StoredGaussian.pivotStep state pivot) pivot.val [] [] [] []) := by
    rw [outerStore_restrict];exact ran
  have result := relocate_executes pivotStepRoutine outerRoles (outerStore state pivot.val counter) time _ localRun
  rw [outerStore_relocate] at result
  exact ⟨time,bounded,result⟩

theorem outerStore_update_counter {q : Nat} (state : GaussianState q) (pivot : Nat) (before after : List Bool) :
    Function.update (outerStore state pivot before) 52 after=outerStore state pivot after := by
  funext r
  by_cases equal : r=52
  · subst r;simp
  · have inside : r.val<52 := by have bound := r.isLt;have different : r.val≠52 := fun h => equal (Fin.ext h);omega
    simp [Function.update_of_ne equal,outerStore,inside]

theorem incrementPivot_executes {q : Nat} (state : GaussianState q) (pivot : Nat) (counter : List Bool) :
    Executes (pushBit (42 : Fin 53) true) (outerStore state pivot counter) 1
      (outerStore state (pivot+1) counter) := by
  have ran := pushBit_executes (42 : Fin 53) true (outerStore state pivot counter)
  convert ran using 1
  funext r;fin_cases r <;>
    simp [outerStore,stateStore,stateSaved,ready,bank,MatrixAxpy.file,RowAxpy.file,List.replicate_succ]

end Counting.StackMachine.GaussianBank
