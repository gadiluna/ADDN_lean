import Counting.StackRealizabilityLevelPrefix
import Counting.StackRealizabilityPreservingPass
import Counting.StackEncodingRelabel

namespace Counting.StackMachine.RealizabilityCheck
open Routine
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

def levelPassRoles : Fin 27 ↪ Fin 36 where
  toFun r := ⟨r.val,by omega⟩
  inj' := by intro a b same;apply Fin.ext;exact congrArg (fun r : Fin 36 => r.val) same

def levelPassBody : Routine 34 := mapRegisters levelPassRoles levelPrefix

def levelPreserved : Routine 34 := preservedPass levelPassBody

/-- Repeated level-mass scans preserve both encoded lists. Copying the lists
and clearing consumed payloads are included in the physical step bound. -/
theorem levelPreserved_executes (store : Store 34) (accepted : Bool) (tail : List Bool)
    (status : store 1=accepted::tail)
    (work : ∀r : Fin 36,r.val<17 → r≠1 → store r=[])
    (e17 : store 17=[]) (e18 : store 18=[]) (e19 : store 19=[]) (e20 : store 20=[])
    (e23 : store 23=[]) (e24 : store 24=[]) (e26 : store 26=[]) (e33 : store 33=[])
    (nodes : List Executable.Node) (values : List Nat) (length : values.length=nodes.length)
    (nodeSuffix weightSuffix : List Bool)
    (nodeInput : store 34=(Encoding.list Encoding.node).encode nodes++nodeSuffix)
    (weightInput : store 35=(Encoding.list Encoding.natural).encode values++weightSuffix)
    (target total : Nat) (level : store 22=target.bits) (e25 : store 25=[])
    (accumulator : store 21=total.bits) :
    ∃ time ≤ 15000*((store 34).length+(store 35).length+total.size+target.size+1)^5,
      Executes levelPreserved store time
        (Function.update store 21 (total+levelRangeSum nodes target 0 values).bits) := by
  let prepared := preparedPassStore store
  let localStore : Store 25 := prepared ∘ levelPassRoles
  have localWork (r : Fin 27) (small : r.val<17) (different : r≠1) : localStore r=[] := by
    have n17 : levelPassRoles r≠17 := by
      intro same
      have equal := congrArg (fun r : Fin 36 => r.val) same
      change r.val=17 at equal
      omega
    have n20 : levelPassRoles r≠20 := by
      intro same
      have equal := congrArg (fun r : Fin 36 => r.val) same
      change r.val=20 at equal
      omega
    have ne1 : levelPassRoles r≠1 := by
      intro same
      apply different
      apply Fin.ext
      exact congrArg (fun r : Fin 36 => r.val) same
    have actual := work (levelPassRoles r) small ne1
    simpa only [localStore,Function.comp_apply,prepared,preparedPassStore,
      Function.update_of_ne n20,Function.update_of_ne n17] using actual
  obtain ⟨time,bound,run⟩ := levelPrefix_executes localStore accepted tail
    (by simpa [localStore,prepared,preparedPassStore,levelPassRoles] using status) localWork
    (by simpa [localStore,prepared,preparedPassStore,levelPassRoles] using e18)
    (by simpa [localStore,prepared,preparedPassStore,levelPassRoles] using e19)
    (by simpa [localStore,prepared,preparedPassStore,levelPassRoles] using e23)
    (by simpa [localStore,prepared,preparedPassStore,levelPassRoles] using e24)
    (by simpa [localStore,prepared,preparedPassStore,levelPassRoles] using e26)
    nodes values length nodeSuffix weightSuffix
    (by simpa [localStore,prepared,preparedPassStore,levelPassRoles] using nodeInput)
    (by simpa [localStore,prepared,preparedPassStore,levelPassRoles] using weightInput)
    target total
    (by simpa [localStore,prepared,preparedPassStore,levelPassRoles] using level)
    (by simpa [localStore,prepared,preparedPassStore,levelPassRoles] using e25)
    (by simpa [localStore,prepared,preparedPassStore,levelPassRoles] using accumulator)
  let scanned := Function.update (Function.update (Function.update prepared
    17 (Encoding.sequence Encoding.node nodes++nodeSuffix)) 20 weightSuffix)
    21 (total+levelRangeSum nodes target 0 values).bits
  have scanRun : Executes levelPassBody prepared time scanned := by
    apply relocate_executes_frame levelPrefix levelPassRoles prepared scanned localStore _ time rfl _ _ run
    · intro r
      fin_cases r <;> simp [scanned,levelPrefixStore,localStore,levelPassRoles]
    · intro r outside
      have n17 : r≠17 := by intro same;subst r;exact outside 17 rfl
      have n20 : r≠20 := by intro same;subst r;exact outside 20 rfl
      have n21 : r≠21 := by intro same;subst r;exact outside 21 rfl
      simp [scanned,n17,n20,n21]
  have execution := preservedPass_executes levelPassBody store scanned time e17 e20 e33 scanRun
  have final : finishedPassStore scanned=Function.update store 21
      (total+levelRangeSum nodes target 0 values).bits := by
    funext r
    fin_cases r <;> simp [finishedPassStore,scanned,prepared,preparedPassStore,e17,e20]
  rw [final] at execution
  have nodeLimit : (scanned 17).length ≤ (store 34).length := by
    simp only [scanned,Function.update_of_ne (by decide : (17:Fin 36)≠21),
      Function.update_of_ne (by decide : (17:Fin 36)≠20),Function.update_self,nodeInput]
    change (Encoding.sequence Encoding.node nodes++nodeSuffix).length ≤
      ((Encoding.natural.encode nodes.length++Encoding.sequence Encoding.node nodes)++nodeSuffix).length
    simp only [List.length_append]
    omega
  have weightLimit : (scanned 20).length ≤ (store 35).length := by
    simp [scanned,weightInput]
  change time ≤ 13000*((store 34).length+(store 35).length+total.size+target.size+1)^5 at bound
  let S := (store 34).length+(store 35).length+total.size+target.size+1
  have linear : S ≤ S^5 := Nat.le_self_pow (by decide) _
  have one : 1 ≤ S^5 := Nat.one_le_pow _ _ (by dsimp only [S];omega)
  exact ⟨_,by change _ ≤ 15000*S^5;dsimp only [S] at linear one ⊢;omega,execution⟩

end Counting.StackMachine.RealizabilityCheck
