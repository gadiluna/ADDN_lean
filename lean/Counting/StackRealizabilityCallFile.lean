import Counting.StackRealizabilityDecision
import Counting.StackRoutineClean

namespace Counting.StackMachine.RealizabilityCall
open Routine

/-- The reusable verifier uses the first hundred cells. Thirty external
cells hold the source encodings and the caller's persistent state. -/
def file (data : Fin 30→List Bool) : Store 128 :=
  fun r => if inside : 100 ≤ r.val then data ⟨r.val-100,by omega⟩ else []

def context : Fin 30 ↪ Fin 130 where
  toFun r := ⟨100+r.val,by omega⟩
  inj' := by
    intro a b same
    apply Fin.ext
    have equal := congrArg (fun r : Fin 130=>r.val) same
    change 100+a.val=100+b.val at equal
    omega

def localRoles : Fin 100 ↪ Fin 130 where
  toFun r := ⟨r.val,by omega⟩
  inj' := by intro a b same;exact Fin.ext (congrArg (fun r:Fin 130=>r.val) same)

@[simp] theorem file_context (data : Fin 30→List Bool) (r : Fin 30) :
    file data (context r)=data r := by simp [file,context]

@[simp] theorem file_local (data : Fin 30→List Bool) (r : Fin 100) :
    file data (localRoles r)=[] := by
  have outside : ¬100 ≤ (localRoles r).val := by
    change ¬100 ≤ r.val
    have := r.isLt
    omega
  simp only [file,dif_neg outside]

theorem file_update (data : Fin 30→List Bool) (r : Fin 30) (value : List Bool) :
    Function.update (file data) (context r) value=file (Function.update data r value) := by
  funext i
  by_cases inside : 100 ≤ i.val
  · by_cases same : i=context r
    · subst i;simp
    · have different : (⟨i.val-100,by omega⟩:Fin 30)≠r := by
        intro equal
        apply same
        apply Fin.ext
        have values := congrArg (fun r : Fin 30=>r.val) equal
        change i.val-100=r.val at values
        change i.val=100+r.val
        omega
      simp [file,inside,same,different]
  · have different : i≠context r := by
      intro equal
      have vals := congrArg (fun r : Fin 130=>r.val) equal
      change i.val=100+r.val at vals
      omega
    simp [file,inside,different]

end Counting.StackMachine.RealizabilityCall
