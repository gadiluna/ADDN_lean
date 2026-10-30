import Counting.StackDagGuards
import Counting.StackEncodingBranch
import Counting.RealizabilityVerifier

namespace Counting.StackMachine.RealizabilityCheck
open Routine EncodingPrograms
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

/-- Binary comparisons branch on their computed flag and preserve all operands. -/
def ifLe (extra : Nat) (roles : Fin 6 ↪ Fin (extra+6))
    (yes no : Routine (extra+4)) : Routine (extra+4) :=
  sequence (Binary.preservingComparison extra roles) (branchRoutine (roles 2) yes no)

theorem ifLe_executes (extra : Nat) (roles : Fin 6 ↪ Fin (extra+6))
    (yes no : Routine (extra+4)) (store result : Store (extra+4)) (time : Nat)
    (a : store (roles 3)=[]) (b : store (roles 4)=[]) (c : store (roles 5)=[])
    (run : Executes (if Binary.compareBits true (store (roles 0)) (store (roles 1)) then yes else no)
      store time result) :
    Executes (ifLe extra roles yes no) store
      (Binary.preservingCompareCost (store (roles 0)) (store (roles 1))+1+(1+time)) result := by
  have compared:=Binary.preservingComparison_executes extra roles store a b c
  let checked:=Function.update store (roles 2)
    (Binary.compareBits true (store (roles 0)) (store (roles 1))::store (roles 2))
  have reset : Function.update checked (roles 2) (store (roles 2))=store := by
    simp only [checked,Function.update_idem,Function.update_eq_self]
  have branch : Executes (branchRoutine (roles 2) yes no) checked (1+time) result := by
    cases flag : Binary.compareBits true (store (roles 0)) (store (roles 1))
    · apply branch_executes_false (roles 2) yes no checked result (store (roles 2)) time
        (by simp [checked,flag])
      rw [reset]
      simpa only [flag,Bool.false_eq_true,if_false] using run
    · apply branch_executes_true (roles 2) yes no checked result (store (roles 2)) time
        (by simp [checked,flag])
      rw [reset]
      simpa only [flag,if_true] using run
  exact compared.sequence branch

private theorem compare_nat (a b : Nat) : Binary.compareBits true a.bits b.bits=decide (a ≤ b) := by
  apply Bool.eq_iff_iff.mpr
  simp only [Binary.compareBits_le,Encoding.value_bits,decide_eq_true_eq]

private theorem bits_injective (a b : Nat) : a.bits=b.bits ↔ a=b := by
  constructor
  · intro same
    simpa only [Encoding.value_bits] using congrArg Encoding.value same
  · rintro rfl; rfl

def roundIdle : Routine 8 := ⟨0,fun _=>.halt⟩

theorem roundIdle_executes (store : Store 8) : Executes roundIdle store 0 store :=
  ⟨⟨0,store⟩,rfl,rfl,rfl⟩

def refinementRoles : Fin 6 ↪ Fin 10 := ⟨![0,1,6,7,8,9],by decide⟩
def fullRoles : Fin 6 ↪ Fin 10 := ⟨![5,4,6,7,8,9],by decide⟩
def noLeavingRoles : Fin 6 ↪ Fin 10 := ⟨![1,0,6,7,8,9],by decide⟩
def balanceRoles : Fin 6 ↪ Fin 10 := ⟨![2,3,6,7,8,9],by decide⟩
def demandRoles : Fin 6 ↪ Fin 10 := ⟨![3,2,6,7,8,9],by decide⟩

def partialRoundGuard : Routine 8 :=
  ifLe 4 noLeavingRoles (DagValidation.leGuard 4 demandRoles) roundIdle

def balanceRoundGuard : Routine 8 :=
  ifLe 4 fullRoles (DagValidation.equalityGuard 4 balanceRoles) partialRoundGuard

/-- Registers 0..5 contain child count, old weight, supply, demand, next-level
visible count and order. Register 6 is the accumulated status; 7..9 are scratch. -/
def roundBoundsGuard : Routine 8 :=
  sequence (DagValidation.leGuard 4 refinementRoles) balanceRoundGuard

def roundBoundsCheck (child weight supply demand visible order : Nat) : Bool :=
  decide (child ≤ weight ∧ (order ≤ visible → supply=demand) ∧
    (visible < order → (weight ≤ child → demand ≤ supply)))

theorem roundBoundsCheck_subtraction (child weight supply demand visible order : Nat) :
    roundBoundsCheck child weight supply demand visible order=
      decide (child ≤ weight ∧ (order-visible=0 → supply=demand) ∧
        (0 < order-visible → (weight-child=0 → demand ≤ supply))) := by
  apply Bool.eq_iff_iff.mpr
  simp only [roundBoundsCheck,decide_eq_true_eq]
  omega

theorem roundBoundsCheck_branch (child weight supply demand visible order : Nat) :
    roundBoundsCheck child weight supply demand visible order=
      (decide (child ≤ weight) &&
        if order ≤ visible then decide (supply=demand)
        else if weight ≤ child then decide (demand ≤ supply) else true) := by
  by_cases full : order ≤ visible <;> by_cases noLeaving : weight ≤ child <;>
    simp [roundBoundsCheck,full,noLeaving,show visible < order ↔ ¬order ≤ visible by omega]

private theorem partialRoundGuard_executes (store : Store 8) (child weight supply demand : Nat)
    (hc : store 0=child.bits) (hw : store 1=weight.bits)
    (hs : store 2=supply.bits) (hd : store 3=demand.bits)
    (accepted : Bool) (tail : List Bool) (status : store 6=accepted::tail)
    (empty : ∀ r : Fin 10,7 ≤ r.val → store r=[]) :
    ∃ time ≤ 30*(child.size+weight.size+supply.size+demand.size+1),
      Executes partialRoundGuard store time
        (Function.update store 6 ((accepted && if weight ≤ child then decide (demand ≤ supply) else true)::tail)) := by
  have conditional (result : Store 8) (time : Nat):=ifLe_executes 4 noLeavingRoles (DagValidation.leGuard 4 demandRoles) roundIdle
    store result time (empty 7 (by decide)) (empty 8 (by decide)) (empty 9 (by decide))
  simp only [noLeavingRoles,Function.Embedding.coeFn_mk,Matrix.cons_val_zero,
    Matrix.cons_val_one,hw,hc,compare_nat,decide_eq_true_eq] at conditional
  have compareBound:=Binary.preservingCompareCost_le weight.bits child.bits
  simp only [Encoding.bits_length] at compareBound
  by_cases noLeaving : weight ≤ child
  · simp only [if_pos noLeaving] at conditional
    have body:=DagValidation.leGuard_executes 4 demandRoles store accepted tail
      status (empty 7 (by decide)) (empty 8 (by decide)) (empty 9 (by decide))
    change Executes (DagValidation.leGuard 4 demandRoles) store
      (Binary.preservingCompareCost (store 3) (store 2)+4)
      (Function.update store 6 ((accepted && Binary.compareBits true (store 3) (store 2))::tail)) at body
    rw [hd,hs,compare_nat] at body
    have bodyBound:=Binary.preservingCompareCost_le demand.bits supply.bits
    simp only [Encoding.bits_length] at bodyBound
    refine ⟨Binary.preservingCompareCost weight.bits child.bits+1+(1+(Binary.preservingCompareCost demand.bits supply.bits+4)),by omega,?_⟩
    simpa only [if_pos noLeaving,partialRoundGuard,noLeavingRoles] using conditional _ _ body
  · simp only [if_neg noLeaving] at conditional
    have body:=roundIdle_executes store
    have final : Function.update store 6 ((accepted && if weight ≤ child then decide (demand ≤ supply) else true)::tail)=store := by
      simp only [if_neg noLeaving,Bool.and_true,←status,Function.update_eq_self]
    rw [final]
    exact ⟨Binary.preservingCompareCost weight.bits child.bits+1+(1+0),by omega,conditional _ _ body⟩

private theorem balanceRoundGuard_executes (store : Store 8)
    (child weight supply demand visible order : Nat)
    (hc : store 0=child.bits) (hw : store 1=weight.bits)
    (hs : store 2=supply.bits) (hd : store 3=demand.bits)
    (hv : store 4=visible.bits) (hn : store 5=order.bits)
    (accepted : Bool) (tail : List Bool) (status : store 6=accepted::tail)
    (empty : ∀ r : Fin 10,7 ≤ r.val → store r=[]) :
    ∃ time ≤ 60*(child.size+weight.size+supply.size+demand.size+visible.size+order.size+1),
      Executes balanceRoundGuard store time
        (Function.update store 6 ((accepted &&
          if order ≤ visible then decide (supply=demand)
          else if weight ≤ child then decide (demand ≤ supply) else true)::tail)) := by
  have conditional (result : Store 8) (time : Nat):=ifLe_executes 4 fullRoles (DagValidation.equalityGuard 4 balanceRoles) partialRoundGuard
    store result time (empty 7 (by decide)) (empty 8 (by decide)) (empty 9 (by decide))
  simp only [fullRoles,Function.Embedding.coeFn_mk,Matrix.cons_val_zero,
    Matrix.cons_val_one,hn,hv,compare_nat,decide_eq_true_eq] at conditional
  have compareBound:=Binary.preservingCompareCost_le order.bits visible.bits
  simp only [Encoding.bits_length] at compareBound
  by_cases full : order ≤ visible
  · simp only [if_pos full] at conditional
    have body:=DagValidation.equalityGuard_executes 4 balanceRoles store accepted tail
      status (empty 7 (by decide)) (empty 8 (by decide)) (empty 9 (by decide))
    change Executes (DagValidation.equalityGuard 4 balanceRoles) store
      (Compare.preservingCost (store 2) (store 3)+4)
      (Function.update store 6 ((accepted && decide (store 2=store 3))::tail)) at body
    simp only [hs,hd,bits_injective] at body
    have bodyBound:=Compare.preservingCost_le supply.bits demand.bits
    simp only [Encoding.bits_length] at bodyBound
    refine ⟨Binary.preservingCompareCost order.bits visible.bits+1+(1+(Compare.preservingCost supply.bits demand.bits+4)),by omega,?_⟩
    simpa only [if_pos full,balanceRoundGuard,fullRoles] using conditional _ _ body
  · simp only [if_neg full] at conditional
    obtain ⟨bodyTime,bodyBound,body⟩:=partialRoundGuard_executes store child weight supply demand
      hc hw hs hd accepted tail status empty
    refine ⟨Binary.preservingCompareCost order.bits visible.bits+1+(1+bodyTime),by omega,?_⟩
    simpa only [if_neg full,balanceRoundGuard,fullRoles] using conditional _ _ body

theorem roundBoundsGuard_executes (store : Store 8)
    (child weight supply demand visible order : Nat)
    (hc : store 0=child.bits) (hw : store 1=weight.bits)
    (hs : store 2=supply.bits) (hd : store 3=demand.bits)
    (hv : store 4=visible.bits) (hn : store 5=order.bits)
    (accepted : Bool) (tail : List Bool) (status : store 6=accepted::tail)
    (empty : ∀ r : Fin 10,7 ≤ r.val → store r=[]) :
    ∃ time ≤ 100*(child.size+weight.size+supply.size+demand.size+visible.size+order.size+1),
      Executes roundBoundsGuard store time
        (Function.update store 6 ((accepted && roundBoundsCheck child weight supply demand visible order)::tail)) := by
  have first:=DagValidation.leGuard_executes 4 refinementRoles store accepted tail status
    (empty 7 (by decide)) (empty 8 (by decide)) (empty 9 (by decide))
  change Executes (DagValidation.leGuard 4 refinementRoles) store
    (Binary.preservingCompareCost (store 0) (store 1)+4)
    (Function.update store 6 ((accepted && Binary.compareBits true (store 0) (store 1))::tail)) at first
  rw [hc,hw,compare_nat] at first
  let middle:=Function.update store 6 ((accepted && decide (child ≤ weight))::tail)
  obtain ⟨time,bound,second⟩:=balanceRoundGuard_executes middle child weight supply demand visible order
    (by simp [middle,hc]) (by simp [middle,hw]) (by simp [middle,hs]) (by simp [middle,hd])
    (by simp [middle,hv]) (by simp [middle,hn]) (accepted && decide (child ≤ weight)) tail (by simp [middle])
    (by intro r hr; have different : r≠6:=by intro same; subst r; simp at hr
        simp [middle,Function.update_of_ne different,empty r hr])
  simp only [middle,Function.update_idem,Bool.and_assoc,←roundBoundsCheck_branch] at second
  have compareBound:=Binary.preservingCompareCost_le child.bits weight.bits
  simp only [Encoding.bits_length] at compareBound
  exact ⟨Binary.preservingCompareCost child.bits weight.bits+4+1+time,by omega,first.sequence second⟩

/-- The binary guard tests exactly the three arithmetic clauses of the actual verifier. -/
theorem roundBoundsCheck_verifier_component (vista : Executable.Vista) (weights : Array Nat)
    (r old order : Nat) :
    roundBoundsCheck (RealizabilityVerifier.childCount vista weights r old)
      (RealizabilityVerifier.weight weights old) (RealizabilityVerifier.supply vista weights r old)
      (RealizabilityVerifier.demand vista weights r old)
      (((Executable.levelNodes vista (r+1)).map (RealizabilityVerifier.weight weights)).sum) order =
    decide (RealizabilityVerifier.childCount vista weights r old ≤ RealizabilityVerifier.weight weights old ∧
      (RealizabilityVerifier.hidden order vista weights r=0 →
        RealizabilityVerifier.supply vista weights r old=RealizabilityVerifier.demand vista weights r old) ∧
      (0 < RealizabilityVerifier.hidden order vista weights r →
        (RealizabilityVerifier.leaving vista weights r old=0 →
          RealizabilityVerifier.demand vista weights r old ≤ RealizabilityVerifier.supply vista weights r old))) :=
  roundBoundsCheck_subtraction _ _ _ _ _ _

end Counting.StackMachine.RealizabilityCheck
