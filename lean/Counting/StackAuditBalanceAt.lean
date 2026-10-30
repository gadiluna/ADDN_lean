import Counting.StackRealizabilityMassSpec
import Counting.StackRealizabilityMassInputBounds
import Counting.StackCompare
import Counting.EncodingNetwork

namespace Counting.StackMachine.AuditBalance
open Routine RealizabilityCheck
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000

def balanceFile (source weights level query status answer : List Bool) : Store 40 :=
  Function.update (massFile source weights level [] query status [] [] []) 0 answer

abbrev checkAt : Routine 40 := sequence massCalculate
  (sequence (ofProgram (Compare.equalityProgram 40 26 37 0)) (clear 21))

/-- Check equality of the two weighted masses at a supplied binary level
and parent index. Both source encodings are preserved, and all three mass
accumulators are physically erased after their comparison. -/
theorem checkAt_executes (source weights : List Bool) (accepted : Bool) (tail : List Bool)
    (nodes : List Executable.Node) (sorted : ∀ node∈nodes,Executable.countsSorted node.incoming=true)
    (values : List Nat) (length : values.length=nodes.length) (nodeSuffix weightSuffix : List Bool)
    (nodeInput : source=(Encoding.list Encoding.node).encode nodes++nodeSuffix)
    (weightInput : weights=(Encoding.list Encoding.natural).encode values++weightSuffix)
    (target old : Nat) :
    ∃ time ≤ 100000100*(source.length+weights.length+target.size+old.size+2)^15,
      Executes checkAt (massFile source weights target.bits [] old.bits (accepted::tail) [] [] []) time
        (balanceFile source weights target.bits old.bits (accepted::tail)
          [decide (demandRangeSum nodes target old 0 values=supplyRangeSum nodes target old 0 values)]) := by
  obtain ⟨massTime,massBound,a⟩ := massCalculate_executes source weights accepted tail nodes sorted values
    length nodeSuffix weightSuffix nodeInput weightInput target old
  let child := childRangeSum nodes target old 0 values
  let demand := demandRangeSum nodes target old 0 values
  let supply := supplyRangeSum nodes target old 0 values
  let computed := massFile source weights target.bits [] old.bits (accepted::tail) child.bits demand.bits supply.bits
  have b := Compare.equality_executes 40 (26:Fin 42) 37 0 (by decide) (by decide) (by decide) computed
  have demandAt : computed 26=demand.bits := by simp [computed,massFile]
  have supplyAt : computed 37=supply.bits := by simp [computed,massFile]
  have outputAt : computed 0=[] := by simp [computed,massFile]
  have injective : demand.bits=supply.bits ↔ demand=supply := by
    constructor
    · intro equal
      have values := congrArg Encoding.value equal
      simpa only [Encoding.value_bits] using values
    · exact congrArg Nat.bits
  rw [demandAt,supplyAt,outputAt] at b
  simp only [injective] at b
  let compared := Function.update
    (massFile source weights target.bits [] old.bits (accepted::tail) child.bits [] []) 0 [decide (demand=supply)]
  have bResult : Function.update (Function.update (Function.update computed 26 []) 37 []) 0
      [decide (demand=supply)]=compared := by
    funext r
    fin_cases r <;> simp [computed,massFile,compared]
  rw [bResult] at b
  have c := clear_executes (21:Fin 42) compared
  have childAt : compared 21=child.bits := by simp [compared,massFile]
  rw [childAt,Encoding.bits_length] at c
  have cResult : Function.update compared 21 []=
      balanceFile source weights target.bits old.bits (accepted::tail) [decide (demand=supply)] := by
    funext r
    fin_cases r <;> simp [compared,massFile,balanceFile]
  rw [cResult] at c
  have comparison := Compare.equalityCost_le demand.bits supply.bits
  simp only [Encoding.bits_length] at comparison
  have masses := massRangeSums_size nodes values length sorted target old
  have inputBound : massInputSize nodes values ≤ source.length+weights.length+target.size+old.size+2 := by
    simp only [massInputSize,nodeInput,weightInput,List.length_append]
    omega
  let S := source.length+weights.length+target.size+old.size+2
  have raised := Nat.pow_le_pow_left inputBound 2
  have sizes : child.size+supply.size+demand.size ≤ 6*S^2 := by
    dsimp only [child,supply,demand]
    change (massInputSize nodes values)^2 ≤ S^2 at raised
    omega
  have positive : 1 ≤ S := by dsimp only [S];omega
  have square : S^2 ≤ S^15 := Nat.pow_le_pow_right positive (by decide)
  have one : 1 ≤ S^15 := Nat.one_le_pow _ _ positive
  refine ⟨_,?_,a.sequence (b.sequence c)⟩
  change massTime ≤ 100000000*S^15 at massBound
  change _ ≤ 100000100*S^15
  omega

/-- On a checked DAG this is exactly one balance equality from the
counting audit, rather than a stronger realization-certificate condition. -/
theorem checkAt_actual (vista : Executable.Vista) (weights : Array Nat)
    (valid : vista.valid=true) (length : weights.size=vista.nodes.size)
    (round old : Nat) (accepted : Bool) (tail : List Bool) :
    ∃ time ≤ 100000100*((Encoding.vista.encode vista).length+
        ((Encoding.array Encoding.natural).encode weights).length+(round+1).size+old.size+2)^15,
      Executes checkAt
        (massFile (Encoding.vista.encode vista) ((Encoding.array Encoding.natural).encode weights)
          (round+1).bits [] old.bits (accepted::tail) [] [] []) time
        (balanceFile (Encoding.vista.encode vista) ((Encoding.array Encoding.natural).encode weights)
          (round+1).bits old.bits (accepted::tail)
          [decide (RealizabilityVerifier.demand vista weights round old=
            RealizabilityVerifier.supply vista weights round old)]) := by
  have sortedAt := mass_sorted_of_valid vista valid
  have sorted (node : Executable.Node) (member : node∈vista.nodes.toList) :
      Executable.countsSorted node.incoming=true := by
    obtain ⟨index,inside,rfl⟩ := Array.mem_iff_getElem.mp (Array.mem_toList_iff.mp member)
    simpa [Executable.Vista.node,inside] using sortedAt index inside
  simpa only [demandRangeSum_vista vista weights round old length sortedAt,
    supplyRangeSum_vista vista weights round old length] using
    checkAt_executes (Encoding.vista.encode vista) ((Encoding.array Encoding.natural).encode weights)
      accepted tail vista.nodes.toList sorted weights.toList
      (by simpa only [Array.length_toList] using length) (Encoding.natural.encode vista.bottom) []
      rfl (by simp [Encoding.array,Encoding.transport,Encoding.list]) (round+1) old

end Counting.StackMachine.AuditBalance
