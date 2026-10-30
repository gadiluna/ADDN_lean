import Counting.StackRealizabilityAccumulate
import Counting.StackDagGuards
import Counting.StackRealizabilityCountsLoop
import Counting.StackEncodingIncomingSpec

namespace Counting.StackMachine.RealizabilityCheck
open Routine EncodingPrograms
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

def initialPositiveRoles : Fin 4 ↪ Fin 10:=⟨![2,4,5,6],by decide⟩
def initialOrderRoles : Fin 6 ↪ Fin 10:=⟨![2,3,4,5,6,7],by decide⟩
def initialLeaderRoles : Fin 6 ↪ Fin 10:=⟨![0,2,4,5,6,7],by decide⟩
def initialCapacityRoles : Fin 6 ↪ Fin 10:=⟨![5,3,4,6,7,8],by decide⟩
def initialAddRoles : Fin 4 ↪ Fin 10:=⟨![5,6,7,8],by decide⟩

/-- Inputs are the two initial counts, the leader count, and the order.
The five temporary registers are restored; only the accumulated status changes. -/
def initialBoundsGuard : Routine 8:=sequence (DagValidation.positivePreserving 6 initialPositiveRoles)
  (sequence (DagValidation.leGuard 4 initialOrderRoles)
    (sequence (DagValidation.leGuard 4 initialLeaderRoles)
      (sequence (ofProgram (ListPrograms.copyProgram 7 1 5 9))
        (sequence (ofProgram (ListPrograms.copyProgram 7 2 6 9))
          (sequence (accumulateAt initialAddRoles)
            (sequence (DagValidation.leGuard 4 initialCapacityRoles) (clear 5)))))))

def initialBoundsCheck (leaders nonleaders ell order : Nat) : Bool:=
  decide (0<ell ∧ ell ≤ order ∧ leaders ≤ ell ∧ nonleaders ≤ order-ell)

theorem initialBoundsCheck_add (leaders nonleaders ell order : Nat) :
    initialBoundsCheck leaders nonleaders ell order=
      (((decide (0<ell) && decide (ell ≤ order)) && decide (leaders ≤ ell)) && decide (nonleaders+ell ≤ order)):=by
  apply Bool.eq_iff_iff.mpr
  simp only [initialBoundsCheck,decide_eq_true_eq,Bool.and_eq_true]
  omega

private theorem positive_bits (value : Nat) : lastPayloadBit false value.bits=decide (0<value):=by
  apply Bool.eq_iff_iff.mpr
  rw [positivePayload_iff]
  simp only [Encoding.value_bits,decide_eq_true_eq]
  have canonical : canonicalPayload value.bits=true:=
    (canonicalPayload_iff _).mpr (by rw [Encoding.value_bits])
  simp [canonical]

private theorem compare_bits (first second : Nat) :
    Binary.compareBits true first.bits second.bits=decide (first ≤ second):=by
  apply Bool.eq_iff_iff.mpr
  simp only [Binary.compareBits_le,Encoding.value_bits,decide_eq_true_eq]

theorem initialBoundsGuard_executes (store : Store 8) (leaders nonleaders ell order : Nat)
    (first : store 0=leaders.bits) (second : store 1=nonleaders.bits)
    (leaderInput : store 2=ell.bits) (orderInput : store 3=order.bits)
    (accepted : Bool) (tail : List Bool) (status : store 4=accepted::tail)
    (empty : ∀ r : Fin 10,5 ≤ r.val → store r=[]) :
    ∃ time  ≤  100*(leaders.size+nonleaders.size+ell.size+order.size+1),
      Executes initialBoundsGuard store time
        (Function.update store 4 ((accepted && initialBoundsCheck leaders nonleaders ell order)::tail)):=by
  let positive:=decide (0<ell)
  let inOrder:=decide (ell ≤ order)
  let leaderBound:=decide (leaders ≤ ell)
  let capacity:=decide (nonleaders+ell ≤ order)
  let afterPositive:=Function.update store 4 ((accepted&&positive)::tail)
  have positiveRun:=DagValidation.positivePreserving_executes 6 initialPositiveRoles store accepted tail
    status (empty 5 (by decide)) (empty 6 (by decide))
  simp only [initialPositiveRoles,Function.Embedding.coeFn_mk,Matrix.cons_val_zero,
    Matrix.cons_val_one,leaderInput,Encoding.bits_length,positive_bits] at positiveRun
  have orderRun:=DagValidation.leGuard_executes 4 initialOrderRoles afterPositive (accepted&&positive) tail
    (by simp [initialOrderRoles,afterPositive]) (by simp [initialOrderRoles,afterPositive,empty])
    (by simp [initialOrderRoles,afterPositive,empty]) (by simp [initialOrderRoles,afterPositive,empty])
  have orderAt : afterPositive 2=ell.bits:=by simp [afterPositive,leaderInput]
  have nAt : afterPositive 3=order.bits:=by simp [afterPositive,orderInput]
  change Executes (DagValidation.leGuard 4 initialOrderRoles) afterPositive
    (Binary.preservingCompareCost (afterPositive 2) (afterPositive 3)+4)
      (Function.update afterPositive 4
        (((accepted&&positive)&&Binary.compareBits true (afterPositive 2) (afterPositive 3))::tail)) at orderRun
  rw [orderAt,nAt,compare_bits] at orderRun
  let afterOrder:=Function.update afterPositive 4 (((accepted&&positive)&&inOrder)::tail)
  have leaderRun:=DagValidation.leGuard_executes 4 initialLeaderRoles afterOrder
    ((accepted&&positive)&&inOrder) tail (by simp [initialLeaderRoles,afterOrder])
    (by simp [initialLeaderRoles,afterOrder,afterPositive,empty])
    (by simp [initialLeaderRoles,afterOrder,afterPositive,empty])
    (by simp [initialLeaderRoles,afterOrder,afterPositive,empty])
  change Executes (DagValidation.leGuard 4 initialLeaderRoles) afterOrder
    (Binary.preservingCompareCost (afterOrder 0) (afterOrder 2)+4)
      (Function.update afterOrder 4
        ((((accepted&&positive)&&inOrder)&&Binary.compareBits true (afterOrder 0) (afterOrder 2))::tail)) at leaderRun
  have leaderAt : afterOrder 0=leaders.bits:=by simp [afterOrder,afterPositive,first]
  have ellAt : afterOrder 2=ell.bits:=by simp [afterOrder,afterPositive,leaderInput]
  rw [leaderAt,ellAt,compare_bits] at leaderRun
  let checked:=Function.update afterOrder 4 ((((accepted&&positive)&&inOrder)&&leaderBound)::tail)
  have copiedFirst:=copy_executes 7 (1:Fin 10) 5 9 (by decide) (by decide) (by decide) checked
    (by simp [checked,afterOrder,afterPositive,empty])
  have firstAt : checked 1=nonleaders.bits:=by simp [checked,afterOrder,afterPositive,second]
  have scratchFirst : checked 5=[]:=by simp [checked,afterOrder,afterPositive,empty]
  rw [firstAt,scratchFirst,List.append_nil,Encoding.bits_length] at copiedFirst
  let copied:=Function.update checked 5 nonleaders.bits
  have copiedSecond:=copy_executes 7 (2:Fin 10) 6 9 (by decide) (by decide) (by decide) copied
    (by simp [copied,checked,afterOrder,afterPositive,empty])
  have secondAt : copied 2=ell.bits:=by simp [copied,checked,afterOrder,afterPositive,leaderInput]
  have scratchSecond : copied 6=[]:=by simp [copied,checked,afterOrder,afterPositive,empty]
  rw [secondAt,scratchSecond,List.append_nil,Encoding.bits_length] at copiedSecond
  let operands:=Function.update copied 6 ell.bits
  obtain ⟨addTime,addBound,addition⟩:=accumulateAt_executes initialAddRoles operands
    (by simp [initialAddRoles,operands,copied,checked,afterOrder,afterPositive,empty])
    (by simp [initialAddRoles,operands,copied,checked,afterOrder,afterPositive,empty])
  change addTime ≤ 11*((operands 5).length+(operands 6).length)+20 at addBound
  change Executes (accumulateAt initialAddRoles) operands addTime
    (Function.update (Function.update operands 5
      (Encoding.value (operands 5)+Encoding.value (operands 6)).bits) 6 []) at addition
  have leftAt : operands 5=nonleaders.bits:=by simp [operands,copied]
  have rightAt : operands 6=ell.bits:=by simp [operands]
  rw [leftAt,rightAt,Encoding.value_bits,Encoding.value_bits] at addition
  rw [leftAt,rightAt,Encoding.bits_length,Encoding.bits_length] at addBound
  let added:=Function.update (Function.update operands 5 (nonleaders+ell).bits) 6 []
  have capacityRun:=DagValidation.leGuard_executes 4 initialCapacityRoles added
    (((accepted&&positive)&&inOrder)&&leaderBound) tail
    (by simp [initialCapacityRoles,added,operands,copied,checked])
    (by simp [initialCapacityRoles,added])
    (by simp [initialCapacityRoles,added,operands,copied,checked,afterOrder,afterPositive,empty])
    (by simp [initialCapacityRoles,added,operands,copied,checked,afterOrder,afterPositive,empty])
  change Executes (DagValidation.leGuard 4 initialCapacityRoles) added
    (Binary.preservingCompareCost (added 5) (added 3)+4)
      (Function.update added 4
        (((((accepted&&positive)&&inOrder)&&leaderBound)&&Binary.compareBits true (added 5) (added 3))::tail)) at capacityRun
  have sumAt : added 5=(nonleaders+ell).bits:=by simp [added]
  have orderAt' : added 3=order.bits:=by simp [added,operands,copied,checked,afterOrder,afterPositive,orderInput]
  rw [sumAt,orderAt',compare_bits] at capacityRun
  let finalStatus:=Function.update added 4
    (((((accepted&&positive)&&inOrder)&&leaderBound)&&capacity)::tail)
  have clearing:=clear_executes (5:Fin 10) finalStatus
  have clearAt : finalStatus 5=(nonleaders+ell).bits:=by simp [finalStatus,added]
  rw [clearAt,Encoding.bits_length] at clearing
  have final : Function.update finalStatus 5 []=
      Function.update store 4 ((accepted&&initialBoundsCheck leaders nonleaders ell order)::tail):=by
    rw [initialBoundsCheck_add]
    funext r
    fin_cases r <;> simp [finalStatus,added,operands,copied,checked,afterOrder,afterPositive,
      positive,inOrder,leaderBound,capacity,empty,Bool.and_assoc]
  rw [final] at clearing
  have orderCost:=Binary.preservingCompareCost_le ell.bits order.bits
  have leaderCost:=Binary.preservingCompareCost_le leaders.bits ell.bits
  have capacityCost:=Binary.preservingCompareCost_le (nonleaders+ell).bits order.bits
  simp only [Encoding.bits_length] at orderCost leaderCost capacityCost
  have sumSize:=nat_add_size_le nonleaders ell
  exact ⟨_,by omega,positiveRun.sequence (orderRun.sequence (leaderRun.sequence
    (copiedFirst.sequence (copiedSecond.sequence (addition.sequence (capacityRun.sequence clearing))))))⟩

end Counting.StackMachine.RealizabilityCheck
