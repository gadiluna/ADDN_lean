import Counting.StackDagReferenceTarget
import Counting.StackDagCoverSpec

namespace Counting.StackMachine.DagValidation
open Routine EncodingPrograms
set_option backward.isDefEq.respectTransparency false

def coverStep : Routine 33:=sequence referenceTarget
  (sequence (incrementRoutine 32 2 26 3) (incrementRoutine 32 2 24 3))

def coverStepStore (store : Store 33) (accepted : Bool) (tail : List Bool)
    (nodes : List Executable.Node) (target : Nat) : Store 33:=
  Function.update (Function.update (Function.update store 1
    ((accepted && !noTableReference target nodes)::tail)) 26 (target+1).bits) 24 (target+2).bits

theorem coverStep_executes (store : Store 33) (accepted : Bool) (tail : List Bool)
    (status : store 1=accepted::tail)
    (work : ∀ r : Fin 35,r.val<17 → r≠1 → store r=[])
    (extraWork : ∀ r : Fin 35,r∈({21,22,23,27,28,30,31}:Finset (Fin 35)) → store r=[])
    (nodes : List Executable.Node) (target : Nat) (inside : target<nodes.length)
    (targetCode : store 26=target.bits) (targetPlus : store 24=(target+1).bits)
    (suffix : List Bool) (source : store 17=Encoding.sequence Encoding.node nodes++suffix)
    (count : (store 25).length=nodes.length) :
    ∃ time ≤ 42000*((store 17).length+1)^4,
      Executes coverStep store time (coverStepStore store accepted tail nodes target) := by
  obtain ⟨checkTime,checkBound,checking⟩:=referenceTarget_executes store accepted tail status work extraWork target
    targetCode targetPlus nodes suffix source count
  let checked:=Function.update store 1 ((accepted && !noTableReference target nodes)::tail)
  obtain ⟨firstTime,firstBound,firstRun⟩:=increment_natural 32 2 26 3
    (by decide) (by decide) (by decide) checked
    (by simp [checked,work]) (by simp [checked,work]) target (by simp [checked,targetCode])
  let middle:=Function.update checked 26 (target+1).bits
  obtain ⟨secondTime,secondBound,secondRun⟩:=increment_natural 32 2 24 3
    (by decide) (by decide) (by decide) middle
    (by simp [middle,checked,work]) (by simp [middle,checked,work]) (target+1) (by simp [middle,checked,targetPlus])
  have nodeBound : nodes.length≤(store 17).length:=by
    have bounded:=node_sequence_count_le nodes
    rw [source,List.length_append]
    omega
  have size : target.size≤target:=Nat.size_le.mpr Nat.lt_two_pow_self
  have plusSize : (target+1).size≤target+1:=Nat.size_le.mpr Nat.lt_two_pow_self
  let S:=(store 17).length+1
  have spos : 1≤S:=by dsimp only [S];omega
  have targetBound : target+1≤S:=by dsimp only [S];omega
  have base : (store 17).length+target.size+1≤2*S:=by dsimp only [S];omega
  have checkLimit : checkTime≤40000*S^4:=by
    calc
      checkTime≤2500*(2*S)^4:=checkBound.trans (by gcongr)
      _=40000*S^4:=by ring
  have linear : S≤S^4:=Nat.le_self_pow (by decide) _
  have one : 1≤S^4:=Nat.one_le_pow _ _ spos
  exact ⟨checkTime+1+(firstTime+1+secondTime),by change _≤42000*S^4;omega,checking.sequence (firstRun.sequence secondRun)⟩

end Counting.StackMachine.DagValidation
