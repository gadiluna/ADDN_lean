import Counting.StackRealizabilitySupplyHeader
import Counting.StackComparePreserving
import Counting.StackDagEmptyGuard
import Counting.StackEncodingGuards

namespace Counting.StackMachine.RealizabilityCheck
open Routine EncodingPrograms
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

def maskOldRoles : Fin 6 ↪ Fin 30:=⟨![0,22,24,4,5,6],by decide⟩
def maskNewRoles : Fin 6 ↪ Fin 30:=⟨![0,23,25,4,5,6],by decide⟩

/-- Binary equality for both adjacent levels, and a constant-time test of
canonical degree positivity. Original payloads are preserved. -/
def maskFields : Routine 28:=sequence (Compare.preservingEquality 24 maskOldRoles)
  (sequence (Compare.preservingEquality 24 maskNewRoles)
    (sequence (DagValidation.emptyFlag 27 26) (negateFlag 28 26)))

def maskFieldsStore (store : Store 28) (node : Executable.Node) (old next : Nat) : Store 28:=
  Function.update (Function.update (Function.update store
    24 (decide (node.level=old)::store 24))
    25 (decide (node.level=next)::store 25))
    26 (decide (0<node.degree)::store 26)

theorem maskFields_executes (store : Store 28) (node : Executable.Node) (old next : Nat)
    (level : store 0=node.level.bits) (oldAt : store 22=old.bits) (nextAt : store 23=next.bits)
    (degree : store 27=node.degree.bits) (e4 : store 4=[]) (e5 : store 5=[]) (e6 : store 6=[]) :
    ∃ time ≤ 40*(node.level.size+old.size+next.size+1),
      Executes maskFields store time (maskFieldsStore store node old next):=by
  have first:=Compare.preservingEquality_executes 24 maskOldRoles store e4 e5 e6
  have firstBound:=Compare.preservingCost_le (store 0) (store 22)
  change Executes (Compare.preservingEquality 24 maskOldRoles) store
    (Compare.preservingCost (store 0) (store 22))
    (Function.update store 24 (decide (store 0=store 22)::store 24)) at first
  rw [level,oldAt] at first
  simp only [Encoding.bits_injective.eq_iff] at first
  rw [level,oldAt,Encoding.bits_length,Encoding.bits_length] at firstBound
  let checkedOld:=Function.update store 24 (decide (node.level=old)::store 24)
  have second:=Compare.preservingEquality_executes 24 maskNewRoles checkedOld
    (by simp [checkedOld,maskNewRoles,e4]) (by simp [checkedOld,maskNewRoles,e5])
    (by simp [checkedOld,maskNewRoles,e6])
  change Executes (Compare.preservingEquality 24 maskNewRoles) checkedOld
    (Compare.preservingCost (checkedOld 0) (checkedOld 23))
    (Function.update checkedOld 25 (decide (checkedOld 0=checkedOld 23)::checkedOld 25)) at second
  have firstAt : checkedOld 0=node.level.bits:=by simp [checkedOld,level]
  have nextValue : checkedOld 23=next.bits:=by simp [checkedOld,nextAt]
  have newTail : checkedOld 25=store 25:=by simp [checkedOld]
  rw [firstAt,nextValue,newTail] at second
  simp only [Encoding.bits_injective.eq_iff] at second
  have secondBound:=Compare.preservingCost_le node.level.bits next.bits
  rw [Encoding.bits_length,Encoding.bits_length] at secondBound
  let checkedNew:=Function.update checkedOld 25 (decide (node.level=next)::store 25)
  have testing:=DagValidation.emptyFlag_executes (27:Fin 30) 26 checkedNew
  have degreeAt : checkedNew 27=node.degree.bits:=by simp [checkedNew,checkedOld,degree]
  have degreeTail : checkedNew 26=store 26:=by simp [checkedNew,checkedOld]
  rw [degreeAt,degreeTail] at testing
  let tested:=Function.update checkedNew 26 (decide (node.degree.bits=[])::store 26)
  have negating:=negateFlag_executes 28 26 tested (decide (node.degree.bits=[])) (store 26) (by simp [tested])
  have positive : (!decide (node.degree.bits=[]))=decide (0<node.degree):=by
    have zero : node.degree.bits=[] ↔ node.degree=0:=by
      constructor
      · intro same
        have equal:=congrArg Encoding.value same
        simpa only [Encoding.value_bits,Encoding.value] using equal
      · intro same;rw [same];rfl
    apply Bool.eq_iff_iff.mpr
    simp only [Bool.not_eq_true',decide_eq_false_iff_not,decide_eq_true_eq,zero]
    omega
  rw [positive] at negating
  have final : Function.update tested 26 (decide (0<node.degree)::store 26)=maskFieldsStore store node old next:=by
    simp [tested,checkedNew,checkedOld,maskFieldsStore]
  rw [final] at negating
  have emptyCost : DagValidation.emptyFlagCost node.degree.bits ≤ 3:=by
    unfold DagValidation.emptyFlagCost
    split_ifs <;> omega
  exact ⟨_,by omega,first.sequence (second.sequence (testing.sequence negating))⟩

end Counting.StackMachine.RealizabilityCheck
