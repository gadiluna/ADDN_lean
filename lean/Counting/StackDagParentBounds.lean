import Counting.StackDagParentCheck

namespace Counting.StackMachine.DagValidation
open Routine EncodingPrograms
set_option maxRecDepth 4096

theorem node_metadata_size_le (node : Executable.Node) :
    (parentCode node).size+node.level.size ≤ (Encoding.node.encode node).length := by
  rw [Encoding.node_length]
  unfold Encoding.nodeBits parentCode
  omega

theorem node_sequence_count_le (values : List Executable.Node) :
    values.length ≤ (Encoding.sequence Encoding.node values).length := by
  induction values with
  | nil=>rfl
  | cons node values ih=>
    have positive : 0<(Encoding.node.encode node).length:=by
      rw [Encoding.node_length]
      unfold Encoding.nodeBits
      omega
    simp only [List.length_cons,Encoding.sequence,List.length_append]
    omega

theorem node_sequence_member_le (values : List Executable.Node) (node : Executable.Node)
    (member : node∈values) :
    (Encoding.node.encode node).length≤(Encoding.sequence Encoding.node values).length := by
  induction values with
  | nil=>simp at member
  | cons first values ih=>
    rcases List.mem_cons.mp member with rfl|inside
    · simp [Encoding.sequence]
    · have tail:=ih inside
      simp only [Encoding.sequence,List.length_append]
      omega

private theorem parent_cost_polynomial (L E i c s d e : Nat)
    (index : i≤L) (indexBits : s ≤ i) (parentLevel : d≤L) (nodeFields : c+e≤E) :
    100*(i+2*c+2)^3+(2*i+3)*2029*(L+1)^3+19*L+38+100*(c+s+d+e+3)≤
      10000*(L+E+1)^4 := by
  let S:=L+E+1
  have first : i+2*c+2≤2*S:=by dsimp [S];omega
  have factor : 2*i+3≤3*S:=by dsimp [S];omega
  have base : L+1≤S:=by dsimp [S];omega
  have preparation : 100*(i+2*c+2)^3≤800*S^3 := by
    calc
      _ ≤ 100*(2*S)^3:=by gcongr
      _ = _:=by ring
  have scanning : (2*i+3)*2029*(L+1)^3≤6087*S^4 := by
    calc
      _ ≤ (3*S)*2029*S^3:=by gcongr
      _ = _:=by ring
  have fields : 100*(c+s+d+e+3)≤300*S:=by dsimp [S];omega
  have linear : 19*L+38≤57*S:=by dsimp [S];omega
  have positive : 1≤S:=by dsimp [S];omega
  have cube : S^3≤S^4:=by exact Nat.pow_le_pow_right positive (by decide)
  have single : S≤S^4:=Nat.le_self_pow (by decide) _
  dsimp only [S] at preparation scanning fields linear cube single
  omega

/-- Uniform bit-length bound for the concrete parent routine. All numeric
indices are bounded by the actual serialized source; the level itself may
be arbitrarily large and contributes only its binary encoding length. -/
theorem binaryParentCheck_polynomial (store : Store 26) (accepted : Bool) (tail : List Bool)
    (status : store 1=accepted::tail)
    (work : ∀ r : Fin 28,r.val<17 → r≠1 → store r=[])
    (extraWork : ∀ r : Fin 28,r∈({18,19,20,26}:Finset (Fin 28)) → store r=[])
    (values : List Executable.Node) (current : Nat) (node : Executable.Node)
    (inside : current<values.length) (suffix : List Bool)
    (source : store 17=Encoding.sequence Encoding.node values++suffix)
    (level : store 21=node.level.bits) (reference : store 22=(parentCode node).bits)
    (leader : store 23=[node.leader]) (currentIndex : store 24=current.bits)
    (budget : (store 25).length=current) :
    ∃ time ≤ 10000*((store 17).length+(Encoding.node.encode node).length+1)^4,
      Executes binaryParentCheck store time (binaryParentStore store accepted tail values current node inside) := by
  obtain ⟨time,bounded,executed⟩:=binaryParentCheck_executes store accepted tail status work extraWork
    values current node inside suffix source level reference leader currentIndex budget
  have count:=node_sequence_count_le values
  have indexBound : current≤(store 17).length:=by rw [source,List.length_append];omega
  have indexSize : current.size≤current:=Nat.size_le.mpr Nat.lt_two_pow_self
  let selected:=selectedParent values current node inside
  have selectedLength : (Encoding.node.encode values[selected]).length≤(store 17).length := by
    have member:=node_sequence_member_le values values[selected] (List.getElem_mem selected.isLt)
    rw [source,List.length_append]
    omega
  have selectedLevel : values[selected].level.size≤(store 17).length:=by
    have fields:=node_metadata_size_le values[selected]
    omega
  have finalBound:=parent_cost_polynomial (store 17).length (Encoding.node.encode node).length current
    (parentCode node).size current.size values[selected].level.size node.level.size
    indexBound indexSize selectedLevel (node_metadata_size_le node)
  change time≤100*(current+2*(parentCode node).size+2)^3+
      (2*current+3)*2029*((store 17).length+1)^3+6*(store 17).length+7*current+
      6*(Encoding.node.encode values[selected]).length+38+
      100*((parentCode node).size+current.size+values[selected].level.size+node.level.size+3) at bounded
  exact ⟨time,by omega,executed⟩

end Counting.StackMachine.DagValidation
