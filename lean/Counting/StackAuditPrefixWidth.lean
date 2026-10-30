import Counting.StackAuditPrefixCountCompare
import Counting.StackAuditPrefixChildFlags

namespace Counting.StackMachine.AuditPrefix
open Routine
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2100000

abbrev widthGuard : Routine 50 := sequence (relocate (countCompare .level) childClassifyRoles)
  (mergeFlag 35 1)

/-- Compare an actual visible-level cardinality with the binary candidate
and conjoin it with the running status. The candidate is never expanded. -/
theorem widthGuard_executes (store : Store 50) (vista : Executable.Vista)
    (level candidate : Nat) (accepted : Bool) (tail : List Bool) (status : store 1=accepted::tail)
    (work : ∀ r : Fin 52,r.val<17 → r≠1 → store r=[])
    (e18 : store 18=[]) (e19 : store 19=[]) (e24 : store 24=[]) (e28 : store 28=[]) (e29 : store 29=[])
    (e31 : store 31=[]) (e32 : store 32=[]) (e33 : store 33=[]) (e34 : store 34=[]) (e35 : store 35=[])
    (suffix : List Bool) (source : store 17=Encoding.sequence Encoding.node vista.nodes.toList++suffix)
    (nodeCount : store 20=List.replicate vista.nodes.size true)
    (levelAt : store 30=level.bits) (candidateAt : store 21=candidate.bits) :
    ∃ time ≤ 31000*((store 17).length+level.size+candidate.size+1)^5,
      Executes widthGuard store time (Function.update store 1
        ((accepted && decide ((Executable.levelNodes vista level).length≤candidate))::tail)) := by
  let localStore:Store 34:=store ∘ childClassifyRoles
  have localWork (r:Fin 36) (small:r.val<17) (different:r≠1) : localStore r=[] := by
    apply work (childClassifyRoles r) small
    intro same;apply different;exact Fin.ext (congrArg (fun q:Fin 52=>q.val) same)
  obtain ⟨time,bound,run⟩:=countCompare_executes .level vista localStore accepted tail status localWork
    e18 e19 e24 e28 e29 e31 e33 e34 e35 suffix source nodeCount level 0 candidate levelAt
    (by simpa [localStore,childClassifyRoles] using e32) candidateAt
  rw [countRange_full_level] at run
  let passed:=decide ((Executable.levelNodes vista level).length≤candidate)
  let checked:=Function.update store 35 [passed]
  have a:Executes (relocate (countCompare .level) childClassifyRoles) store time checked := by
    apply relocate_executes_frame (countCompare .level) childClassifyRoles store checked localStore _ time rfl _ _ run
    · intro r;fin_cases r <;> simp [checked,localStore,childClassifyRoles,passed]
    · intro r outside
      have n35:r≠35 := by intro same;subst r;exact outside 35 rfl
      simp [checked,n35]
  have b:=mergeFlag_executes 35 1 (by decide) (by decide) (by decide) checked
    (by simp [checked,work]) passed accepted tail (by simp [checked]) (by simp [checked,status])
  have final : Function.update (Function.update checked 35 []) 1 ((accepted && passed)::tail)=
      Function.update store 1 ((accepted && passed)::tail) := by
    simp only [checked,Function.update_idem]
    rw [←e35,Function.update_eq_self]
  rw [final] at b
  change time≤30000*((store 17).length+level.size+Nat.size 0+candidate.size+1)^5 at bound
  simp only [Nat.size_zero,Nat.add_zero] at bound
  have one : 1≤((store 17).length+level.size+candidate.size+1)^5 := Nat.one_le_pow _ _ (by omega)
  exact ⟨_,by omega,a.sequence b⟩

abbrev rootLeaderGuard : Routine 50 := sequence (relocate (countPositive .leader) childClassifyRoles)
  (mergeFlag 35 1)

/-- The root leader-presence check is an actual scan of the node table. -/
theorem rootLeaderGuard_executes (store : Store 50) (vista : Executable.Vista)
    (accepted : Bool) (tail : List Bool) (status : store 1=accepted::tail)
    (work : ∀ r : Fin 52,r.val<17 → r≠1 → store r=[])
    (e18 : store 18=[]) (e19 : store 19=[]) (e28 : store 28=[]) (e29 : store 29=[])
    (e30 : store 30=[]) (e31 : store 31=[]) (e32 : store 32=[]) (e33 : store 33=[])
    (e34 : store 34=[]) (e35 : store 35=[])
    (suffix : List Bool) (source : store 17=Encoding.sequence Encoding.node vista.nodes.toList++suffix)
    (nodeCount : store 20=List.replicate vista.nodes.size true) :
    ∃ time ≤ 21000*((store 17).length+1)^5,
      Executes rootLeaderGuard store time (Function.update store 1
        ((accepted && (Executable.levelNodes vista 0).any (fun i=>(vista.node i).leader))::tail)) := by
  let localStore:Store 34:=store ∘ childClassifyRoles
  have localWork (r:Fin 36) (small:r.val<17) (different:r≠1) : localStore r=[] := by
    apply work (childClassifyRoles r) small
    intro same;apply different;exact Fin.ext (congrArg (fun q:Fin 52=>q.val) same)
  obtain ⟨time,bound,run⟩:=countPositive_executes .leader vista localStore accepted tail status localWork
    e18 e19 e28 e29 e31 e33 e34 e35 suffix source nodeCount 0 0
    (by simpa [localStore,childClassifyRoles] using e30)
    (by simpa [localStore,childClassifyRoles] using e32)
  have predicate : decide (0<countRange vista .leader 0 0 0 vista.nodes.size)=
      (Executable.levelNodes vista 0).any (fun i=>(vista.node i).leader) := by
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq,countRange_leader_positive]
  rw [predicate] at run
  let passed:=(Executable.levelNodes vista 0).any (fun i=>(vista.node i).leader)
  let checked:=Function.update store 35 [passed]
  have a:Executes (relocate (countPositive .leader) childClassifyRoles) store time checked := by
    apply relocate_executes_frame (countPositive .leader) childClassifyRoles store checked localStore _ time rfl _ _ run
    · intro r;fin_cases r <;> simp [checked,localStore,childClassifyRoles,passed]
    · intro r outside
      have n35:r≠35 := by intro same;subst r;exact outside 35 rfl
      simp [checked,n35]
  have b:=mergeFlag_executes 35 1 (by decide) (by decide) (by decide) checked
    (by simp [checked,work]) passed accepted tail (by simp [checked]) (by simp [checked,status])
  have final : Function.update (Function.update checked 35 []) 1 ((accepted && passed)::tail)=
      Function.update store 1 ((accepted && passed)::tail) := by
    simp only [checked,Function.update_idem]
    rw [←e35,Function.update_eq_self]
  rw [final] at b
  change time≤20010*((store 17).length+Nat.size 0+Nat.size 0+1)^5 at bound
  simp only [Nat.size_zero,Nat.add_zero] at bound
  have one : 1≤((store 17).length+1)^5 := Nat.one_le_pow _ _ (by omega)
  exact ⟨_,by omega,a.sequence b⟩

end Counting.StackMachine.AuditPrefix
