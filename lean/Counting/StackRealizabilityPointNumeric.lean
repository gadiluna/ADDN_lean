import Counting.StackRealizabilityMassFlags
import Counting.StackReadBranch
import Counting.StackEncodingRelabel

namespace Counting.StackMachine.RealizabilityCheck
open Routine
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

def pointLeavingRoles : Fin 6 ↪ Fin 60 := ⟨![43,21,46,0,2,3],by decide⟩
def pointDeficitRoles : Fin 6 ↪ Fin 60 := ⟨![37,26,47,0,2,3],by decide⟩
def pointGuardRoles : Fin 10 ↪ Fin 60 := ⟨![21,43,37,26,45,44,1,0,2,3],by decide⟩

def pointGuard : Routine 58 := mapRegisters pointGuardRoles roundBoundsGuard

def pointConditionalGuard : Routine 58 := branchRead 50 pointGuard (skip 58)

/-- Only nodes belonging to the old level contribute arithmetic obligations.
The branch reads an actual stored mask bit and restores it. -/
theorem pointConditionalGuard_executes (store : Store 58)
    (child weight supply demand visible order : Nat)
    (hc : store 21=child.bits) (hw : store 43=weight.bits)
    (hs : store 37=supply.bits) (hd : store 26=demand.bits)
    (hv : store 45=visible.bits) (hn : store 44=order.bits)
    (accepted active : Bool) (tail maskTail : List Bool)
    (status : store 1=accepted::tail) (mask : store 50=active::maskTail)
    (e0 : store 0=[]) (e2 : store 2=[]) (e3 : store 3=[]) :
    ∃ time ≤ 100*(child.size+weight.size+supply.size+demand.size+visible.size+order.size+1)+3,
      Executes pointConditionalGuard store time (Function.update store 1
        ((accepted && (if active then roundBoundsCheck child weight supply demand visible order else true))::tail)) := by
  cases active with
  | false =>
    have run := skip_executes store
    have conditional := branchRead_executes (50:Fin 60) pointGuard (skip 58) false maskTail store store 0 mask run
    have final : Function.update store 1 ((accepted && (if false then roundBoundsCheck child weight supply demand visible order else true))::tail)=store := by
      simp only [Bool.false_eq_true,if_false,Bool.and_true,←status,Function.update_eq_self]
    rw [final]
    exact ⟨3,by omega,conditional⟩
  | true =>
    let localStore : Store 8 := store ∘ pointGuardRoles
    have work (r : Fin 10) (lo : 7≤r.val) : localStore r=[] := by
      fin_cases r <;> simp_all [localStore,pointGuardRoles]
    obtain ⟨time,bound,run⟩ := roundBoundsGuard_executes localStore child weight supply demand visible order
      (by simpa [localStore,pointGuardRoles] using hc) (by simpa [localStore,pointGuardRoles] using hw)
      (by simpa [localStore,pointGuardRoles] using hs) (by simpa [localStore,pointGuardRoles] using hd)
      (by simpa [localStore,pointGuardRoles] using hv) (by simpa [localStore,pointGuardRoles] using hn)
      accepted tail (by simpa [localStore,pointGuardRoles] using status) work
    let final := Function.update store 1 ((accepted && roundBoundsCheck child weight supply demand visible order)::tail)
    have guardRun : Executes pointGuard store time final := by
      apply relocate_executes_frame roundBoundsGuard pointGuardRoles store final localStore _ time rfl _ _ run
      · intro r;fin_cases r <;> simp [final,localStore,pointGuardRoles]
      · intro r outside
        have different : r≠1 := by intro same;subst r;exact outside 6 rfl
        simp [final,different]
    have conditional := branchRead_executes (50:Fin 60) pointGuard (skip 58) true maskTail store final time mask guardRun
    exact ⟨time+3,by omega,conditional⟩

def pointNumeric : Routine 58 := sequence (differencePositive 54 pointLeavingRoles)
  (sequence (differencePositive 54 pointDeficitRoles) pointConditionalGuard)

def pointNumericStore (store : Store 58) (child weight supply demand visible order : Nat)
    (accepted active : Bool) (tail : List Bool) : Store 58 :=
  Function.update (Function.update (Function.update store 46
    (decide (0<weight-child)::store 46)) 47 (decide (demand<supply)::store 47))
    1 ((accepted && (if active then roundBoundsCheck child weight supply demand visible order else true))::tail)

theorem pointNumeric_executes (store : Store 58)
    (child weight supply demand visible order : Nat)
    (hc : store 21=child.bits) (hw : store 43=weight.bits)
    (hs : store 37=supply.bits) (hd : store 26=demand.bits)
    (hv : store 45=visible.bits) (hn : store 44=order.bits)
    (accepted active : Bool) (tail maskTail : List Bool)
    (status : store 1=accepted::tail) (mask : store 50=active::maskTail)
    (e0 : store 0=[]) (e2 : store 2=[]) (e3 : store 3=[]) :
    ∃ time ≤ 200*(child.size+weight.size+supply.size+demand.size+visible.size+order.size+1),
      Executes pointNumeric store time (pointNumericStore store child weight supply demand visible order accepted active tail) := by
  have leaving := differencePositive_executes 54 pointLeavingRoles store weight child hw hc e0 e2 e3
  let left := Function.update store 46 (decide (0<weight-child)::store 46)
  have deficit := differencePositive_executes 54 pointDeficitRoles left supply demand
    (by simp [left,pointDeficitRoles,hs]) (by simp [left,pointDeficitRoles,hd])
    (by simp [left,pointDeficitRoles,e0]) (by simp [left,pointDeficitRoles,e2])
    (by simp [left,pointDeficitRoles,e3])
  change Executes (differencePositive 54 pointDeficitRoles) left
    (Binary.preservingCompareCost supply.bits demand.bits+3)
    (Function.update left 47 (decide (0<supply-demand)::left 47)) at deficit
  have positive : (0<supply-demand) ↔ demand<supply := by omega
  have left47 : left 47=store 47 := by simp [left]
  rw [left47] at deficit
  simp only [positive] at deficit
  let ready := Function.update left 47 (decide (demand<supply)::store 47)
  obtain ⟨guardTime,guardBound,guardRun⟩ := pointConditionalGuard_executes ready
    child weight supply demand visible order
    (by simp [ready,left,hc]) (by simp [ready,left,hw]) (by simp [ready,left,hs])
    (by simp [ready,left,hd]) (by simp [ready,left,hv]) (by simp [ready,left,hn])
    accepted active tail maskTail (by simp [ready,left,status]) (by simp [ready,left,mask])
    (by simp [ready,left,e0]) (by simp [ready,left,e2]) (by simp [ready,left,e3])
  have leavingBound := Binary.preservingCompareCost_le weight.bits child.bits
  have deficitBound := Binary.preservingCompareCost_le supply.bits demand.bits
  simp only [Encoding.bits_length] at leavingBound deficitBound
  have execution := leaving.sequence (deficit.sequence guardRun)
  exact ⟨_,by omega,execution⟩

end Counting.StackMachine.RealizabilityCheck
