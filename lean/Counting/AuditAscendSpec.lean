import Counting.StackDagParentBounds

namespace Counting.StackMachine.AuditAscend
open EncodingPrograms

def indexCode (reference : Option Nat) : Nat := reference.map (·+1) |>.getD 0

def nextCode (vista : Executable.Vista) (code : Nat) : Nat :=
  if code=0 then 0 else indexCode (vista.node (code-1)).parent

def walkCode (vista : Executable.Vista) : Nat → Nat → Nat
  | 0,code => code
  | steps+1,code => walkCode vista steps (nextCode vista code)

/-- A None reference is absorbing; the zero-step case preserves even an
out-of-range Some index, exactly as the executable ascend function. -/
theorem walkCode_ascend (vista : Executable.Vista) (steps : Nat) (reference : Option Nat) :
    walkCode vista steps (indexCode reference)=indexCode (reference.bind (Executable.ascend vista steps)) := by
  induction steps generalizing reference with
  | zero => cases reference <;> rfl
  | succ steps ih =>
    cases reference with
    | none =>
      change walkCode vista steps 0=0
      exact ih none
    | some index =>
      simpa only [walkCode,indexCode,Option.map_some,Option.getD_some,nextCode,
        Nat.add_eq_zero_iff,one_ne_zero,and_false,if_false,Nat.add_sub_cancel,
        Option.bind_some,Executable.ascend] using ih (vista.node index).parent

theorem nextCode_size (vista : Executable.Vista) (code : Nat) :
    (nextCode vista code).size ≤ (Encoding.sequence Encoding.node vista.nodes.toList).length := by
  by_cases zero : code=0
  · simp [nextCode,zero]
  · rw [nextCode,if_neg zero]
    by_cases inside : code-1<vista.nodes.size
    · let selected:=vista.nodes[code-1]
      have metadata:=DagValidation.node_metadata_size_le selected
      have member : selected∈vista.nodes.toList := by
        exact Array.getElem_mem_toList inside
      have bound:=DagValidation.node_sequence_member_le vista.nodes.toList selected member
      have nodeEq : vista.node (code-1)=selected := by
        simp [Executable.Vista.node,Array.getElem?_eq_getElem inside,selected]
      rw [nodeEq]
      change (DagValidation.parentCode selected).size ≤ _
      omega
    · have absent : vista.node (code-1)=default := by
        simp [Executable.Vista.node,Array.getElem?_eq_none (by omega : vista.nodes.size≤code-1)]
      rw [absent]
      change 0≤_
      omega

/-- Every intermediate index is bounded in bit width by the original
reference and the encoded node table; numeric parent indices need not fit. -/
theorem walkCode_size (vista : Executable.Vista) (steps code : Nat) :
    (walkCode vista steps code).size ≤
      max code.size (Encoding.sequence Encoding.node vista.nodes.toList).length := by
  induction steps generalizing code with
  | zero => exact Nat.le_max_left _ _
  | succ steps ih =>
    have after:=ih (nextCode vista code)
    have next:=nextCode_size vista code
    change (walkCode vista steps (nextCode vista code)).size ≤ _
    omega

end Counting.StackMachine.AuditAscend

