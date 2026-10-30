import Counting.StackRealizabilityChildPreserved
import Counting.StackFramedWrite
import Counting.StackFrameReplaceArray

namespace Counting.StackMachine.AuditPropagation
open Routine
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

def writeRoles : Fin 6 ↪ Fin 36 := ⟨![35,31,21,2,3,4],by decide⟩

/-- A child-mass scan followed by a real replacement in the serialized
weight array. The supplied index is the loop's bounded unary node index. -/
abbrev updateNode : Routine 34 := sequence RealizabilityCheck.childPreserved
  (FieldAccess.writePayload 30 writeRoles)

theorem childRangeSum_size (nodes : List Executable.Node) (target old start : Nat) (values : List Nat) :
    (RealizabilityCheck.childRangeSum nodes target old start values).size ≤
      (Encoding.sequence Encoding.natural values).length := by
  induction values generalizing start with
  | nil => simp [RealizabilityCheck.childRangeSum,Encoding.sequence]
  | cons value values ih =>
    have bounded := RealizabilityCheck.child_total_size (nodes[start]?.getD default) target old
      (RealizabilityCheck.childRangeSum nodes target old (start+1) values) value
    have tail := ih (start+1)
    rw [Nat.add_comm] at bounded
    simpa only [RealizabilityCheck.childRangeSum,Encoding.sequence,List.length_append,
      Encoding.natural_length] using (show
        (RealizabilityCheck.childContribution (nodes[start]?.getD default) target old value+
          RealizabilityCheck.childRangeSum nodes target old (start+1) values).size ≤
        2*value.size+1+(Encoding.sequence Encoding.natural values).length by omega)

/-- No well-formedness assumption is needed for a single update. Its source
and destination are the actual serialized DAG and natural array, and its
child sum is exactly the one used by `propagateWeights`. -/
theorem updateNode_executes (store : Store 34) (accepted : Bool) (tail : List Bool)
    (status : store 1=accepted::tail)
    (work : ∀ r : Fin 36,r.val<17 → r≠1 → store r=[])
    (e17 : store 17=[]) (e18 : store 18=[]) (e19 : store 19=[]) (e20 : store 20=[])
    (e21 : store 21=[]) (e23 : store 23=[]) (e24 : store 24=[]) (e26 : store 26=[]) (e33 : store 33=[])
    (vista : Executable.Vista) (weights : Array Nat) (length : weights.size=vista.nodes.size)
    (nodeInput : store 34=Encoding.vista.encode vista)
    (weightInput : store 35=(Encoding.array Encoding.natural).encode weights)
    (r old : Nat) (inside : old<weights.size)
    (level : store 22=(r+1).bits) (parent : store 25=(old+1).bits)
    (index : store 31=List.replicate (old+1) true) :
    ∃ time ≤ 15000*((store 34).length+(store 35).length+(r+1).size+(old+1).size+1)^5+
        22*(store 35).length+3*(old+1)+22,
      Executes updateNode store time
        (Function.update (Function.update store 31 []) 35
          ((Encoding.array Encoding.natural).encode
            (weights.setIfInBounds old (RealizabilityVerifier.childCount vista weights r old)))) := by
  have nodeWord : store 34=(Encoding.list Encoding.node).encode vista.nodes.toList++
      Encoding.natural.encode vista.bottom := by
    simpa only [Encoding.vista,Encoding.transport,Encoding.product,Encoding.array] using nodeInput
  have weightWord : store 35=(Encoding.list Encoding.natural).encode weights.toList++[] := by
    simpa only [List.append_nil,Encoding.array,Encoding.transport] using weightInput
  obtain ⟨scanTime,scanBound,scanning⟩ := RealizabilityCheck.childPreserved_executes store accepted tail status work
    e17 e18 e19 e20 e23 e24 e26 e33 vista.nodes.toList weights.toList
    (by simpa only [Array.length_toList] using length) (Encoding.natural.encode vista.bottom) []
    nodeWord weightWord (r+1) old 0 level parent e21
  rw [Nat.zero_add,RealizabilityCheck.childRangeSum_vista vista weights r old length] at scanning
  let total := RealizabilityVerifier.childCount vista weights r old
  let scanned := Function.update store 21 total.bits
  obtain ⟨writeTime,writeBound,writing⟩ := FieldAccess.writePayload_executes 30 writeRoles scanned
    (by simp [writeRoles,scanned,work]) (by simp [writeRoles,scanned,work]) (by simp [writeRoles,scanned,work])
  have source : scanned (writeRoles 0)=(Encoding.array Encoding.natural).encode weights := by
    simp [writeRoles,scanned,weightInput]
  have counter : scanned (writeRoles 1)=List.replicate (old+1) true := by simp [writeRoles,scanned,index]
  have payload : scanned (writeRoles 2)=total.bits := by simp [writeRoles,scanned]
  have output : FieldAccess.writePayloadResult writeRoles scanned=
      Function.update (Function.update store 31 []) 35
        ((Encoding.array Encoding.natural).encode (weights.setIfInBounds old total)) := by
    unfold FieldAccess.writePayloadResult
    rw [source,counter,payload,List.length_replicate]
    change Function.update (Function.update (Function.update scanned 31 []) 21 []) 35
      (FieldAccess.replaceFieldWord ((Encoding.array Encoding.natural).encode weights) (old+1)
        (Encoding.natural.encode total))=_
    rw [FieldAccess.replaceFieldWord_naturalArray weights old total inside]
    funext target
    by_cases a : target=35 <;> by_cases b : target=31 <;> by_cases c : target=21 <;>
      simp [scanned,a,b,c,e21]
  rw [output] at writing
  refine ⟨_,?_,scanning.sequence writing⟩
  rw [source,counter,payload,List.length_replicate,Encoding.bits_length,←weightInput] at writeBound
  have totalSize := childRangeSum_size vista.nodes.toList (r+1) old 0 weights.toList
  rw [RealizabilityCheck.childRangeSum_vista vista weights r old length] at totalSize
  have fieldBound : (Encoding.sequence Encoding.natural weights.toList).length ≤ (store 35).length := by
    rw [weightWord,List.length_append]
    change _ ≤ (Encoding.natural.encode weights.toList.length++Encoding.sequence Encoding.natural weights.toList).length+0
    rw [List.length_append]
    omega
  change total.size ≤ _ at totalSize
  change scanTime ≤ 15000*((store 34).length+(store 35).length+0+(r+1).size+(old+1).size+1)^5 at scanBound
  simp only [Nat.add_zero] at scanBound
  omega


/-- The update bound is polynomial in the serialized words and the actual
unary field index supplied by the bounded node loop. -/
theorem updateNode_cost_polynomial (nodes weights level parent index : Nat) :
    15000*(nodes+weights+level+parent+1)^5+22*weights+3*index+22 ≤
      17000*(nodes+weights+level+parent+index+1)^5 := by
  let size := nodes+weights+level+parent+index+1
  have raised : (nodes+weights+level+parent+1)^5 ≤ size^5 :=
    Nat.pow_le_pow_left (by dsimp only [size];omega) 5
  have linear : size ≤ size^5 := Nat.le_self_pow (by decide) _
  have one : 1 ≤ size^5 := Nat.one_le_pow _ _ (by dsimp only [size];omega)
  have weightSize : weights ≤ size := by dsimp only [size];omega
  have indexSize : index ≤ size := by dsimp only [size];omega
  change _ ≤ 17000*size^5
  omega

end Counting.StackMachine.AuditPropagation
