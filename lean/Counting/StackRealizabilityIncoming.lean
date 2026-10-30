import Counting.StackAnchorFind
import Counting.StackDagEmptyGuard
import Counting.StackEncodingGuards
import Counting.StackDagClean
import Counting.EncodingRecognitionBounds

namespace Counting.StackMachine.RealizabilityCheck
open Routine EncodingPrograms
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

def positiveBitsFlag (source flag : Fin (registers+2)) : Routine registers:=
  sequence (DagValidation.emptyFlag source flag) (negateFlag registers flag)

theorem positiveBitsFlag_executes (source flag : Fin (registers+2)) (store : Store registers)
    (value : Nat) (contents : store source=value.bits) :
    ∃ time ≤ 6, Executes (positiveBitsFlag source flag) store time
      (Function.update store flag (decide (0<value)::store flag)):=by
  have testing:=DagValidation.emptyFlag_executes source flag store
  rw [contents] at testing
  let tested:=Function.update store flag (decide (value.bits=[])::store flag)
  have negating:=negateFlag_executes registers flag tested (decide (value.bits=[])) (store flag) (by simp [tested])
  have positive : (!decide (value.bits=[]))=decide (0<value):=by
    have zero : value.bits=[] ↔ value=0:=by
      constructor
      · intro same
        have equal:=congrArg Encoding.value same
        simpa only [Encoding.value_bits,Encoding.value] using equal
      · intro same;rw [same];rfl
    apply Bool.eq_iff_iff.mpr
    simp only [Bool.not_eq_true',decide_eq_false_iff_not,decide_eq_true_eq,zero]
    omega
  rw [positive] at negating
  have same : Function.update tested flag (decide (0<value)::store flag)=
      Function.update store flag (decide (0<value)::store flag):=by simp [tested]
  rw [same] at negating
  have bound : DagValidation.emptyFlagCost value.bits ≤ 3:=by
    unfold DagValidation.emptyFlagCost
    split_ifs <;> omega
  exact ⟨_,by omega,testing.sequence negating⟩

/-- Consume the canonical incoming list and emit whether the actual first
matching count is positive. Duplicate sources and zero counts have exactly
the same behavior as `Executable.countFrom`. -/
def incomingPositive : Routine 19:=sequence AnchorFind.lookup
  (sequence (positiveBitsFlag 18 19) (clear 18))

theorem incomingPositive_executes (node : Executable.Node) (query : Nat) (suffix : List Bool) :
    ∃ time ≤ 6000*((Encoding.node.encode node).length+suffix.length+query.size+1)^3,
      Executes incomingPositive
        (AnchorFind.bank ((Encoding.list (Encoding.product Encoding.natural Encoding.natural)).encode node.incoming++suffix)
          query.bits [] [] [] []) time
        (AnchorFind.bank suffix query.bits [] [decide (0<Executable.countFrom node query)] [] []):=by
  obtain ⟨lookupTime,lookupBound,lookupRun⟩:=AnchorFind.lookup_countFrom node query suffix
  let count:=Executable.countFrom node query
  let looked:=AnchorFind.bank suffix query.bits count.bits [] [] []
  obtain ⟨positiveTime,positiveBound,positiveRun⟩:=positiveBitsFlag_executes (18:Fin 21) 19 looked count (by simp [looked,AnchorFind.bank])
  have flagEmpty : looked 19=[]:=by simp [looked,AnchorFind.bank]
  rw [flagEmpty] at positiveRun
  let tested:=Function.update looked 19 [decide (0<count)]
  have clearing:=clear_executes (18:Fin 21) tested
  have countAt : tested 18=count.bits:=by simp [tested,looked,AnchorFind.bank]
  rw [countAt,Encoding.bits_length] at clearing
  have final : Function.update tested 18 []=AnchorFind.bank suffix query.bits [] [decide (0<count)] [] []:=by
    funext r
    fin_cases r <;> simp [tested,looked,AnchorFind.bank]
  rw [final] at clearing
  have suffixBound:=DagValidation.nodeSuffix_length_le node
  have incomingBound : ((Encoding.list (Encoding.product Encoding.natural Encoding.natural)).encode node.incoming).length ≤
      (Encoding.node.encode node).length:=by
    unfold DagValidation.nodeSuffix at suffixBound
    simp only [List.length_append] at suffixBound
    omega
  have countSize : count.size ≤ (Encoding.node.encode node).length:=by
    simpa only [Encoding.node_length] using Encoding.redBits_le_node node query
  let S:=(Encoding.node.encode node).length+suffix.length+query.size+1
  have lookupLimit : lookupTime ≤ 5000*S^3:=by
    apply lookupBound.trans
    apply Nat.mul_le_mul_left
    apply Nat.pow_le_pow_left
    change ((Encoding.list (Encoding.product Encoding.natural Encoding.natural)).encode node.incoming++suffix).length+query.size+1 ≤ S
    simp only [List.length_append]
    dsimp only [S]
    omega
  have linear : S ≤ S^3:=Nat.le_self_pow (by decide) _
  have one : 1 ≤ S^3:=Nat.one_le_pow _ _ (by dsimp only [S];omega)
  exact ⟨_,by change _ ≤ 6000*S^3;dsimp only [S] at lookupLimit linear one ⊢;omega,
    lookupRun.sequence (positiveRun.sequence clearing)⟩

end Counting.StackMachine.RealizabilityCheck
