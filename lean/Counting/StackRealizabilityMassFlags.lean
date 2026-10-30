import Counting.StackRealizabilityRoundGuards

namespace Counting.StackMachine.RealizabilityCheck
open Routine EncodingPrograms
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

/-- Strict positivity of a truncated difference, without constructing the
subtraction. The comparison preserves both binary operands and its scratch. -/
def differencePositive (extra : Nat) (roles : Fin 6 ↪ Fin (extra+6)) : Routine (extra+4):=
  sequence (Binary.preservingComparison extra roles) (negateFlag (extra+4) (roles 2))

theorem differencePositive_executes (extra : Nat) (roles : Fin 6 ↪ Fin (extra+6))
    (store : Store (extra+4)) (first second : Nat)
    (a : store (roles 0)=first.bits) (b : store (roles 1)=second.bits)
    (e3 : store (roles 3)=[]) (e4 : store (roles 4)=[]) (e5 : store (roles 5)=[]) :
    Executes (differencePositive extra roles) store
      (Binary.preservingCompareCost first.bits second.bits+3)
      (Function.update store (roles 2) (decide (0<first-second)::store (roles 2))):=by
  have comparing:=Binary.preservingComparison_executes extra roles store e3 e4 e5
  rw [a,b] at comparing
  let checked:=Function.update store (roles 2)
    (Binary.compareBits true first.bits second.bits::store (roles 2))
  have negating:=negateFlag_executes (extra+4) (roles 2) checked
    (Binary.compareBits true first.bits second.bits) (store (roles 2)) (by simp [checked])
  have answer : (!Binary.compareBits true first.bits second.bits)=decide (0<first-second):=by
    apply Bool.eq_iff_iff.mpr
    simp only [Bool.not_eq_true',decide_eq_true_eq]
    have correct:=Binary.compareBits_le first.bits second.bits
    rw [Encoding.value_bits,Encoding.value_bits] at correct
    cases flag : Binary.compareBits true first.bits second.bits <;> simp_all
  simp only [checked,Function.update_idem,answer] at negating
  exact comparing.sequence negating

def leavingFlagRoles : Fin 6 ↪ Fin 12:=⟨![1,0,6,9,10,11],by decide⟩
def deficitFlagRoles : Fin 6 ↪ Fin 12:=⟨![2,3,7,9,10,11],by decide⟩
def outsideFlagRoles : Fin 6 ↪ Fin 12:=⟨![5,4,8,9,10,11],by decide⟩

/-- Six canonical numeric payloads, followed by three output stacks and
three empty work registers. Only the new Boolean results are added. -/
def massFlags : Routine 10:=sequence (differencePositive 6 leavingFlagRoles)
  (sequence (differencePositive 6 deficitFlagRoles) (differencePositive 6 outsideFlagRoles))

def massFlagsStore (store : Store 10) (child weight supply demand visible order : Nat) : Store 10:=
  Function.update (Function.update (Function.update store
    6 (decide (0<weight-child)::store 6))
    7 (decide (demand<supply)::store 7))
    8 (decide (0<order-visible)::store 8)

theorem massFlags_executes (store : Store 10) (child weight supply demand visible order : Nat)
    (hc : store 0=child.bits) (hw : store 1=weight.bits)
    (hs : store 2=supply.bits) (hd : store 3=demand.bits)
    (hv : store 4=visible.bits) (hn : store 5=order.bits)
    (e9 : store 9=[]) (e10 : store 10=[]) (e11 : store 11=[]) :
    ∃ time ≤ 50*(child.size+weight.size+supply.size+demand.size+visible.size+order.size+1),
      Executes massFlags store time (massFlagsStore store child weight supply demand visible order):=by
  have first:=differencePositive_executes 6 leavingFlagRoles store weight child hw hc e9 e10 e11
  let left:=Function.update store 6 (decide (0<weight-child)::store 6)
  have second:=differencePositive_executes 6 deficitFlagRoles left supply demand
    (by simp [left,deficitFlagRoles,hs]) (by simp [left,deficitFlagRoles,hd])
    (by simp [left,deficitFlagRoles,e9]) (by simp [left,deficitFlagRoles,e10])
    (by simp [left,deficitFlagRoles,e11])
  have deficit : (0<supply-demand) ↔ demand<supply:=by omega
  change Executes (differencePositive 6 deficitFlagRoles) left
    (Binary.preservingCompareCost supply.bits demand.bits+3)
    (Function.update left 7 (decide (0<supply-demand)::left 7)) at second
  have leftTail : left 7=store 7:=by simp [left]
  rw [leftTail] at second
  simp only [deficit] at second
  let middle:=Function.update left 7 (decide (demand<supply)::store 7)
  have third:=differencePositive_executes 6 outsideFlagRoles middle order visible
    (by simp [middle,left,outsideFlagRoles,hn]) (by simp [middle,left,outsideFlagRoles,hv])
    (by simp [middle,left,outsideFlagRoles,e9]) (by simp [middle,left,outsideFlagRoles,e10])
    (by simp [middle,left,outsideFlagRoles,e11])
  have outsideTail : middle (outsideFlagRoles 2)=store 8:=by simp [middle,left,outsideFlagRoles]
  rw [outsideTail] at third
  have firstBound:=Binary.preservingCompareCost_le weight.bits child.bits
  have secondBound:=Binary.preservingCompareCost_le supply.bits demand.bits
  have thirdBound:=Binary.preservingCompareCost_le order.bits visible.bits
  simp only [Encoding.bits_length] at firstBound secondBound thirdBound
  have execution:=first.sequence (second.sequence third)
  exact ⟨_,by omega,execution⟩

/-- These are exactly the three numerical fields used in the compact graph.
No inequality about total mass or refinement is needed for this identity. -/
theorem massFlags_verifier_component (vista : Executable.Vista) (weights : Array Nat)
    (round old order : Nat) (store : Store 10) :
    massFlagsStore store (RealizabilityVerifier.childCount vista weights round old)
      (RealizabilityVerifier.weight weights old) (RealizabilityVerifier.supply vista weights round old)
      (RealizabilityVerifier.demand vista weights round old)
      (((Executable.levelNodes vista (round+1)).map (RealizabilityVerifier.weight weights)).sum) order=
    Function.update (Function.update (Function.update store
      6 (decide (0<RealizabilityVerifier.leaving vista weights round old)::store 6))
      7 (decide (RealizabilityVerifier.demand vista weights round old<
        RealizabilityVerifier.supply vista weights round old)::store 7))
      8 (decide (0<RealizabilityVerifier.hidden order vista weights round)::store 8):=rfl

end Counting.StackMachine.RealizabilityCheck
