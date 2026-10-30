import Counting.StackDagReferenceLookup
import Counting.StackBinaryPredecessor
import Counting.StackEncodingFrameStore
import Counting.StackDagIncrement
import Counting.PropagationEncodingBounds

namespace Counting.StackMachine.DagUpdate
open Routine EncodingPrograms
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000

def parentPredRoles : Binary.PredWorkspace 12 := ⟨![1,3,4,5,6,7,8,9],by decide⟩
def parentLookupRoles : ReferenceWorkspace 6 := ⟨![0,4,2,3,5,6,7,8,9,10,11,12,13,14],by decide⟩

abbrev remapParentPositive : Routine 18 := sequence (Binary.predecessor 12 parentPredRoles)
  (sequence (frameRoutine 17 3 4 19)
    (sequence (referenceLookup 6 parentLookupRoles)
      (sequence (DagValidation.incrementRoutine 17 3 2 19) (clear 4))))

/-- The predecessor query, bounded lookup and successor output all run on
binary strings. The complete mapping and original parent code survive. -/
theorem remapParentPositive_executes (store : Store 18) (mapping : List Nat) (code : Nat)
    (source : store 0=(Encoding.list Encoding.natural).encode mapping)
    (query : store 1=code.bits)
    (empty : ∀ r : Fin 20,r≠0 → r≠1 → store r=[]) :
    ∃ time ≤ 2000*((store 0).length+code.size+1)^3,
      Executes remapParentPositive store time
        (Function.update store 2 ((mapping[code-1]?.getD 0)+1).bits) := by
  obtain ⟨predTime,predBound,a⟩:=Binary.predecessor_executes 12 parentPredRoles store code
    (by simp [parentPredRoles,query]) (by
      intro i member;fin_cases i <;> simp_all [parentPredRoles])
  let previous:=Function.update store 3 (code-1).bits
  change Executes _ store predTime previous at a
  have b:=frame_executes_updates 17 (3:Fin 20) 4 19 (by decide) (by decide) (by decide) previous
    (by simp [previous,empty])
  let framed:=Function.update store 4 (Encoding.natural.encode (code-1))
  have bResult : Function.update (Function.update previous 3 []) 4
      (Encoding.frame (previous 3)++previous 4)=framed := by
    funext r
    by_cases a:r=3 <;> by_cases b:r=4 <;> simp [previous,framed,a,b,empty,Encoding.natural]
  rw [bResult] at b
  change Executes _ previous (5*(code-1).bits.length+4) framed at b
  obtain ⟨lookupTime,lookupBound,c⟩:=referenceLookup_executes 6 parentLookupRoles framed mapping (code-1)
    (by simp [framed,parentLookupRoles,source]) (by simp [framed,parentLookupRoles]) (by
      intro i a b c;fin_cases i <;> simp_all [framed,parentLookupRoles])
  let value:=mapping[code-1]?.getD 0
  let found:=Function.update framed 2 value.bits
  change Executes _ framed lookupTime
    (Function.update framed 2 (value.bits++framed 2)) at c
  have emptyOutput : framed 2=[] := by simp [framed,empty]
  rw [emptyOutput,List.append_nil] at c
  obtain ⟨incTime,incBound,d⟩:=DagValidation.increment_natural 17 (3:Fin 20) 2 19
    (by decide) (by decide) (by decide) found (by simp [found,framed,empty])
    (by simp [found,framed,empty]) value (by simp [found])
  let incremented:=Function.update framed 2 (value+1).bits
  have dResult : Function.update found 2 (value+1).bits=incremented := by simp [found,incremented]
  rw [dResult] at d
  have e:=clear_executes (4:Fin 20) incremented
  have headerAt : incremented 4=Encoding.natural.encode (code-1) := by simp [incremented,framed]
  rw [headerAt] at e
  have eResult : Function.update incremented 4 []=Function.update store 2 (value+1).bits := by
    funext r
    by_cases a:r=4 <;> by_cases b:r=2 <;> simp [incremented,framed,a,b,empty]
  rw [eResult] at e
  have valueBits : value.size ≤ (store 0).length := by
    have arrayBound:=Encoding.naturalArray_entry_size_le mapping.toArray (code-1)
    simpa only [value,List.getElem?_toArray,Encoding.array,Encoding.transport,List.toList_toArray,source] using arrayBound
  have predBits : (code-1).size ≤ code.size := Nat.size_le_size (Nat.sub_le _ _)
  change lookupTime ≤ 200*((store 0).length+(Encoding.natural.encode (code-1)).length+1)^3 at lookupBound
  simp only [Encoding.natural_length] at lookupBound
  have raised:=lookupBound.trans (Nat.mul_le_mul_left 200 (Nat.pow_le_pow_left
    (by omega : (store 0).length+(2*(code-1).size+1)+1 ≤ 2*((store 0).length+code.size+1)) 3))
  have linear : (store 0).length+code.size+1 ≤ ((store 0).length+code.size+1)^3 := Nat.le_self_pow (by decide) _
  refine ⟨_,?_,a.sequence (b.sequence (c.sequence (d.sequence e)))⟩
  simp only [Encoding.bits_length,Encoding.natural_length]
  nlinarith only [raised,linear,predBound,incBound,valueBits,predBits,Nat.zero_le code.size]

end Counting.StackMachine.DagUpdate
