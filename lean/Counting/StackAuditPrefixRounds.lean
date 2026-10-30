import Counting.StackAuditPropagationRounds

namespace Counting.StackMachine.AuditPrefix
open Routine
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

def prefixRoundRoles : Fin 44 ↪ Fin 52 :=
  ⟨fun r=>if r=20 then 40 else if r=39 then 42 else if r=40 then 20
    else if r=41 then 45 else if r=42 then 39 else if r=43 then 51
    else ⟨r.val,by omega⟩,by decide⟩

abbrev prepareRounds : Routine 50 := relocate AuditPropagation.preparePropagationRounds prefixRoundRoles

/-- Reuse the verified bounded conversion on the encoded last-round
payload. Its unary output is capped by the actual stored-node budget even
when the round label is arbitrarily large. -/
theorem prepareRounds_executes (store : Store 50) (last n : Nat)
    (lastAt : store 39=last.bits) (countAt : store 20=List.replicate n true)
    (empty : ∀ i : Fin 52,i∈({0,2,3,4,5,6,7,8,9,10,13,45,51}:Finset (Fin 52)) → store i=[]) :
    ∃ time ≤ 1000*(n+last.size+1)^3,Executes prepareRounds store time
      (Function.update store 45 (List.replicate (min last n) true)) := by
  let localStore:Store 42:=store ∘ prefixRoundRoles
  obtain ⟨time,bound,run⟩:=AuditPropagation.preparePropagationRounds_executes localStore last n
    (by simpa [localStore,prefixRoundRoles] using lastAt)
    (by simpa [localStore,prefixRoundRoles] using countAt) (by
      intro i member
      fin_cases i <;> simp_all [localStore,prefixRoundRoles])
  refine ⟨time,bound,?_⟩
  apply relocate_executes_frame AuditPropagation.preparePropagationRounds prefixRoundRoles store
    (Function.update store 45 (List.replicate (min last n) true)) localStore _ time rfl _ _ run
  · intro i;fin_cases i <;> simp [localStore,prefixRoundRoles]
  · intro r outside
    have different:r≠45 := by intro same;subst r;exact outside 41 rfl
    simp [different]

end Counting.StackMachine.AuditPrefix
