import Counting.StackDagRedReference

namespace Counting.StackMachine.DagValidation
open Routine EncodingPrograms
set_option maxRecDepth 4096

private theorem red_cost_polynomial (L i p pnext d e h : Nat)
    (index : i≤L) (successorSize : pnext≤p+1) (selectedCode : e≤L) (selectedLevel : h≤L) :
    4*p+9+100*(i+2*pnext+2)^3+(2*i+3)*2029*(L+1)^3+6*L+7*i+6*e+72+16*h+6*d≤
      20000*(L+p+d+1)^4 := by
  let S:=L+p+d+1
  have conversion : i+2*pnext+2≤4*S:=by dsimp [S];omega
  have factor : 2*i+3≤3*S:=by dsimp [S];omega
  have base : L+1≤S:=by dsimp [S];omega
  have preparation : 100*(i+2*pnext+2)^3≤6400*S^3 := by
    calc
      _ ≤ 100*(4*S)^3:=by gcongr
      _ = _:=by ring
  have scanning : (2*i+3)*2029*(L+1)^3≤6087*S^4 := by
    calc
      _ ≤ (3*S)*2029*S^3:=by gcongr
      _ = _:=by ring
  have linear : 4*p+9+6*L+7*i+6*e+72+16*h+6*d≤81*S:=by dsimp [S];omega
  have positive : 1≤S:=by dsimp [S];omega
  have cube : S^3≤S^4:=Nat.pow_le_pow_right positive (by decide)
  have single : S≤S^4:=Nat.le_self_pow (by decide) _
  dsimp only [S] at preparation scanning linear cube single
  omega

theorem redReferenceCheck_polynomial (store : Store 26) (accepted : Bool) (tail : List Bool)
    (status : store 1=accepted::tail)
    (work : ∀ r : Fin 28,r.val<17 → r≠1 → store r=[])
    (extraWork : ∀ r : Fin 28,r∈({18,19,20,26}:Finset (Fin 28)) → store r=[])
    (values : List Executable.Node) (current targetLevel sourceIndex : Nat)
    (inside : current<values.length) (suffix : List Bool)
    (source : store 17=Encoding.sequence Encoding.node values++suffix)
    (level : store 21=targetLevel.bits) (reference : store 22=sourceIndex.bits)
    (budget : (store 25).length=current) :
    ∃ time ≤ 20000*((store 17).length+sourceIndex.size+targetLevel.size+1)^4,
      Executes redReferenceCheck store time
        (redReferenceStore store accepted tail values current targetLevel sourceIndex inside) := by
  obtain ⟨time,bounded,executed⟩:=redReferenceCheck_executes store accepted tail status work extraWork
    values current targetLevel sourceIndex inside suffix source level reference budget
  have count:=node_sequence_count_le values
  have indexBound : current≤(store 17).length:=by rw [source,List.length_append];omega
  let selected:=selectedRed values current sourceIndex inside
  have selectedLength : (Encoding.node.encode values[selected]).length≤(store 17).length := by
    have member:=node_sequence_member_le values values[selected] (List.getElem_mem selected.isLt)
    rw [source,List.length_append]
    omega
  have selectedLevel : values[selected].level.size≤(store 17).length:=by
    have fields:=node_metadata_size_le values[selected]
    omega
  have successorSize : (sourceIndex+1).size≤ sourceIndex.size+1 := by
    have length:=increment_length_le sourceIndex.bits
    simpa only [Machine.increment_bits,Encoding.bits_length] using length
  have finalBound:=red_cost_polynomial (store 17).length current sourceIndex.size (sourceIndex+1).size
    targetLevel.size (Encoding.node.encode values[selected]).length values[selected].level.size
    indexBound successorSize selectedLength selectedLevel
  exact ⟨time,bounded.trans finalBound,executed⟩

theorem redCondition_vista (vista : Executable.Vista) (current sourceIndex : Nat) :
    redCondition vista.nodes.toList current (vista.node current).level sourceIndex=
      (sourceIndex<current && (vista.node sourceIndex).level+1==(vista.node current).level) := by
  simp [redCondition,Executable.Vista.node]

end Counting.StackMachine.DagValidation
