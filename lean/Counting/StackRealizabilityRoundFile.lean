import Counting.StackRealizabilityPointTables
import Counting.StackRealizabilityMaskSlots
import Counting.StackRealizabilityOutsideVector

namespace Counting.StackMachine.RealizabilityCheck
open Routine

/-- Fixed scratch space and twenty named context cells for one round. The
context is serialized input or tables computed by charged subroutines. -/
def roundFile (data : Fin 20→List Bool) : Store 98 :=
  fun r => if inside : 80 ≤ r.val then data ⟨r.val-80,by omega⟩ else []

def roundContext : Fin 20 ↪ Fin 100 where
  toFun r := ⟨80+r.val,by omega⟩
  inj' := by
    intro a b same
    apply Fin.ext
    have equal := congrArg (fun r : Fin 100=>r.val) same
    change 80+a.val=80+b.val at equal
    omega

@[simp] theorem roundFile_context (data : Fin 20→List Bool) (r : Fin 20) :
    roundFile data (roundContext r)=data r := by simp [roundFile,roundContext]

theorem roundFile_update (data : Fin 20→List Bool) (r : Fin 20) (value : List Bool) :
    Function.update (roundFile data) (roundContext r) value=roundFile (Function.update data r value) := by
  funext i
  by_cases inside : 80 ≤ i.val
  · by_cases same : i=roundContext r
    · subst i;simp
    · have different : (⟨i.val-80,by omega⟩:Fin 20)≠r := by
        intro equal
        apply same
        apply Fin.ext
        have values := congrArg (fun r : Fin 20=>r.val) equal
        change i.val-80=r.val at values
        change i.val=80+r.val
        omega
      simp [roundFile,inside,same,different]
  · have different : i≠roundContext r := by
      intro equal
      have vals := congrArg (fun r : Fin 100=>r.val) equal
      change i.val=80+r.val at vals
      omega
    simp [roundFile,inside,different]

end Counting.StackMachine.RealizabilityCheck
