import Counting.StackAuditPropagationIndex
import Counting.StackAuditPropagationStep

namespace Counting.StackMachine.AuditPropagation
open Routine
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000

/-- Keep the outer node table and traversal counter protected while the
child scan uses separate temporary copies. -/
def updateCurrentRoles : Fin 36 ↪ Fin 40 :=
  ⟨fun r=>⟨if r.val=17 then 37 else if r.val=18 then 38 else r.val,by
    split_ifs <;> have := r.isLt <;> omega⟩,by
    intro a b equal
    have same := congrArg (fun r:Fin 40=>r.val) equal
    dsimp only at same
    apply Fin.ext
    split_ifs at same <;> have := a.isLt <;> have := b.isLt <;> omega⟩

abbrev updateCurrent : Routine 38 := sequence prepareNodeIndex
  (sequence (relocate updateNode updateCurrentRoles) (clear 25))

/-- A complete selected-node update preserves the outer node traversal,
constructs both index representations and erases the binary parent query. -/
theorem updateCurrent_executes (store : Store 38) (accepted : Bool) (tail : List Bool)
    (status : store 1=accepted::tail)
    (work : ∀ r : Fin 40,r.val<17 → r≠1 → store r=[])
    (e19 : store 19=[]) (e20 : store 20=[]) (e21 : store 21=[])
    (e23 : store 23=[]) (e24 : store 24=[]) (e25 : store 25=[])
    (e26 : store 26=[]) (e31 : store 31=[]) (e33 : store 33=[])
    (e37 : store 37=[]) (e38 : store 38=[])
    (vista : Executable.Vista) (weights : Array Nat) (length : weights.size=vista.nodes.size)
    (nodeInput : store 34=Encoding.vista.encode vista)
    (weightInput : store 35=(Encoding.array Encoding.natural).encode weights)
    (r old : Nat) (inside : old<weights.size)
    (level : store 22=(r+1).bits) (counter : store 18=List.replicate old true) :
    ∃ time ≤ 20000*((store 34).length+(store 35).length+(r+1).size+old+2)^5,
      Executes updateCurrent store time
        (Function.update store 35 ((Encoding.array Encoding.natural).encode
          (weights.setIfInBounds old (RealizabilityVerifier.childCount vista weights r old)))) := by
  obtain ⟨prepareTime,prepareBound,a⟩ := prepareNodeIndex_executes store old counter
    (work _ (by decide) (by decide)) e25 e26 e31
  let prepared := Function.update (Function.update store 31 (List.replicate (old+1) true)) 25 (old+1).bits
  let localStore : Store 34 := prepared ∘ updateCurrentRoles
  have localWork (i : Fin 36) (small : i.val<17) (different : i≠1) : localStore i=[] := by
    have n17 : i.val≠17 := by omega
    have n18 : i.val≠18 := by omega
    have roleSmall : (updateCurrentRoles i).val<17 := by simp [updateCurrentRoles,n17,n18,small]
    have roleDifferent : updateCurrentRoles i≠1 := by
      intro same
      apply different
      apply Fin.ext
      have sameVal := congrArg (fun j:Fin 40=>j.val) same
      simpa [updateCurrentRoles,n17,n18] using sameVal
    have n25 : updateCurrentRoles i≠25 := by intro same;rw [same] at roleSmall;norm_num at roleSmall
    have n31 : updateCurrentRoles i≠31 := by intro same;rw [same] at roleSmall;norm_num at roleSmall
    simp [localStore,prepared,n25,n31,work _ roleSmall roleDifferent]
  obtain ⟨updateTime,updateBound,body⟩ := updateNode_executes localStore accepted tail
    (by simpa [localStore,prepared,updateCurrentRoles] using status) localWork
    (by simp [localStore,prepared,updateCurrentRoles,e37]) (by simp [localStore,prepared,updateCurrentRoles,e38])
    (by simp [localStore,prepared,updateCurrentRoles,e19]) (by simp [localStore,prepared,updateCurrentRoles,e20])
    (by simp [localStore,prepared,updateCurrentRoles,e21]) (by simp [localStore,prepared,updateCurrentRoles,e23])
    (by simp [localStore,prepared,updateCurrentRoles,e24]) (by simp [localStore,prepared,updateCurrentRoles,e26])
    (by simp [localStore,prepared,updateCurrentRoles,e33]) vista weights length
    (by simpa [localStore,prepared,updateCurrentRoles] using nodeInput)
    (by simpa [localStore,prepared,updateCurrentRoles] using weightInput) r old inside
    (by simpa [localStore,prepared,updateCurrentRoles] using level)
    (by simp [localStore,prepared,updateCurrentRoles]) (by simp [localStore,prepared,updateCurrentRoles])
  let resultWord := (Encoding.array Encoding.natural).encode
    (weights.setIfInBounds old (RealizabilityVerifier.childCount vista weights r old))
  let updated := Function.update (Function.update prepared 31 []) 35 resultWord
  have b : Executes (relocate updateNode updateCurrentRoles) prepared updateTime updated := by
    apply relocate_executes_frame updateNode updateCurrentRoles _ _ _ _ updateTime rfl _ _ body
    · intro i;fin_cases i <;> simp [updated,localStore,updateCurrentRoles,resultWord]
    · intro i outside
      have n31 : i≠31 := by intro same;subst i;exact outside 31 rfl
      have n35 : i≠35 := by intro same;subst i;exact outside 35 rfl
      simp [updated,n31,n35]
  have c := clear_executes (25:Fin 40) updated
  have queryAt : updated 25=(old+1).bits := by simp [updated,prepared]
  rw [queryAt,Encoding.bits_length] at c
  have finish : Function.update updated 25 []=Function.update store 35 resultWord := by
    funext i
    by_cases i25 : i=25 <;> by_cases i31 : i=31 <;> by_cases i35 : i=35 <;>
      simp [updated,prepared,i25,i31,i35,e25,e31]
  rw [finish] at c
  refine ⟨_,?_,a.sequence (b.sequence c)⟩
  have nodeAt : localStore 34=store 34 := by simp [localStore,prepared,updateCurrentRoles]
  have weightAt : localStore 35=store 35 := by simp [localStore,prepared,updateCurrentRoles]
  rw [nodeAt,weightAt] at updateBound
  have binary : (old+1).size ≤ old+1 := Nat.size_le.mpr Nat.lt_two_pow_self
  let size := (store 34).length+(store 35).length+(r+1).size+old+2
  have raised : ((store 34).length+(store 35).length+(r+1).size+(old+1).size+1)^5 ≤ size^5 :=
    Nat.pow_le_pow_left (by dsimp only [size];omega) 5
  have one : 1 ≤ size := by dsimp only [size];omega
  have indexSize : old+1 ≤ size := by dsimp only [size];omega
  have weightSize : (store 35).length ≤ size := by dsimp only [size];omega
  have p2 : (old+1)^2 ≤ size^2 := Nat.pow_le_pow_left indexSize 2
  have p25 : size^2 ≤ size^5 := Nat.pow_le_pow_right one (by decide)
  have linear : size ≤ size^5 := Nat.le_self_pow (by decide) _
  have positive : 1 ≤ size^5 := Nat.one_le_pow _ _ one
  change _ ≤ 20000*size^5
  omega

end Counting.StackMachine.AuditPropagation
