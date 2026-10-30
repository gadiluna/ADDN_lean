import Counting.StackDagImportStep
import Counting.StackEncodingListAppendBounds
import Counting.DagImportPrefixBounds

namespace Counting.StackMachine.DagUpdate.Import
open EncodingPrograms
set_option backward.isDefEq.respectTransparency false

private theorem intern_query_length_le (pool : Array Executable.Node) (node : Executable.Node) :
    (Encoding.node.encode node).length ≤
      ((Encoding.array Encoding.node).encode (Executable.intern pool node).1).length := by
  let result:=Executable.intern pool node
  have inside : result.2 < result.1.size:=Executable.intern_index_lt pool node
  have equal:=Executable.intern_node pool node
  have member : node∈result.1.toList := by
    apply List.mem_iff_getElem.mpr
    refine ⟨result.2,by simpa only [Array.length_toList] using inside,?_⟩
    change result.1[result.2]?.getD default=node at equal
    simp only [Array.getElem?_eq_getElem inside,Option.getD_some] at equal
    simpa only [Array.getElem_toList] using equal
  exact Encoding.array_member_length_le _ _ _ member

/-- Bound the actual step budget using serialized current and next states.
The queried signature already occurs in the interning result, so its
encoding is bounded by that result even when a prior node is reused. -/
theorem stepBudget_cap (mapping : Array Nat) (pool : Array Executable.Node)
    (node : Executable.Node) (sourceLength cap : Nat) (positive : 1 ≤ cap)
    (mappingBound : ((Encoding.array Encoding.natural).encode mapping).length ≤ cap)
    (poolBound : ((Encoding.array Encoding.node).encode pool).length ≤ cap)
    (nodeBound : (Encoding.node.encode node).length ≤ cap)
    (sourceBound : sourceLength ≤ cap)
    (nextPoolBound : ((Encoding.array Encoding.node).encode
      (Executable.intern pool (Executable.referenceMap mapping node)).1).length ≤ cap)
    (nextMappingBound : ((Encoding.array Encoding.natural).encode
      (mapping.push (Executable.intern pool (Executable.referenceMap mapping node)).2)).length ≤ cap) :
    stepBudget mapping pool node sourceLength ≤ 100000000000000*cap^7 := by
  let result:=Executable.intern pool (Executable.referenceMap mapping node)
  let M:=((Encoding.array Encoding.natural).encode mapping).length
  let P:=((Encoding.array Encoding.node).encode pool).length
  let Q:=(Encoding.node.encode (Executable.referenceMap mapping node)).length
  let R:=((Encoding.array Encoding.node).encode result.1).length
  let I:=result.2.size
  let T:=((Encoding.array Encoding.natural).encode (mapping.push result.2)).length
  have queryBound : Q ≤ cap:= (intern_query_length_le pool (Executable.referenceMap mapping node)).trans nextPoolBound
  have indexInside : result.2 < result.1.size:=Executable.intern_index_lt pool (Executable.referenceMap mapping node)
  have resultCount : result.1.size ≤ R:=Encoding.array_size_le_length _ _
    (fun n _=>Encoding.node_positive_length n)
  have indexBound : I ≤ cap :=
    (Nat.size_le.mpr Nat.lt_two_pow_self).trans
      ((Nat.le_of_lt indexInside).trans (resultCount.trans nextPoolBound))
  have mappingCount : mapping.size ≤ cap :=
    (Encoding.array_size_le_length Encoding.natural mapping (by intro n _;rw [Encoding.natural_length];omega)).trans mappingBound
  have appendBound:=appendCanonicalBudget_polynomial Encoding.natural mapping.toList result.2
  simp only [Array.length_toList,Encoding.natural_length] at appendBound
  change appendCanonicalBudget Encoding.natural mapping.toList result.2 ≤
    200*(mapping.size+M+(2*I+1)+1)^2 at appendBound
  have appendPower:=Nat.pow_le_pow_left
    (show mapping.size+M+(2*I+1)+1 ≤ 6*cap by dsimp only [M,I] at *;omega) 2
  have parsePower:=Nat.pow_le_pow_left (show sourceLength+1 ≤ 2*cap by omega) 3
  have mapPower:=Nat.pow_le_pow_left
    (show (Encoding.node.encode node).length+M+1 ≤ 3*cap by dsimp only [M];omega) 7
  have internPower:=Nat.pow_le_pow_left
    (show P+Q+1 ≤ 3*cap by dsimp only [P] at *;omega) 4
  have two : cap^2 ≤ cap^7:=Nat.pow_le_pow_right positive (by decide)
  have three : cap^3 ≤ cap^7:=Nat.pow_le_pow_right positive (by decide)
  have four : cap^4 ≤ cap^7:=Nat.pow_le_pow_right positive (by decide)
  have linear : cap ≤ cap^7:=Nat.le_self_pow (by decide) _
  have one : 1 ≤ cap^7:=Nat.one_le_pow _ _ positive
  simp only [stepBudget,mapInternBudget,commitBudget,List.length_nil,Encoding.bits_length]
  change 2100*(sourceLength+1)^3+
    (30000000000*((Encoding.node.encode node).length+0+M+1)^7+
      8000*(P+Q+1)^4+12*0+12*M+7*Q+6*P+6*R+6*I+43)+
    (appendCanonicalBudget Encoding.natural mapping.toList result.2+7*I+M+P+6*T+6*R+24)+2 ≤ _
  change M ≤ cap at mappingBound
  change P ≤ cap at poolBound
  change R ≤ cap at nextPoolBound
  change T ≤ cap at nextMappingBound
  nlinarith only [appendBound,appendPower,parsePower,mapPower,internPower,two,three,four,
    linear,one,mappingBound,poolBound,queryBound,indexBound,nextPoolBound,nextMappingBound]

def importStepCoefficient : Nat:=100000000000000*20^7

/-- Every step of one import shares the same degree-fourteen bound in
the original pool, source list and retained input-stream budget. -/
theorem stepBudget_prefix (pool : Array Executable.Node) (nodes : List Executable.Node)
    (index sourceLength : Nat) (inside : index < nodes.length) :
    stepBudget (Executable.importPrefixState pool nodes index).2
      (Executable.importPrefixState pool nodes index).1 nodes[index] sourceLength ≤
        importStepCoefficient*(((Encoding.array Encoding.node).encode pool).length+
          ((Encoding.list Encoding.node).encode nodes).length+sourceLength+1)^14 := by
  let state:=Executable.importPrefixState pool nodes index
  let K:=((Encoding.array Encoding.node).encode pool).length+
    ((Encoding.list Encoding.node).encode nodes).length+sourceLength+1
  let cap:=20*K^2
  have positive : 1 ≤ K := by dsimp only [K];omega
  have linear : K ≤ K^2:=Nat.le_self_pow (by decide) _
  have one : 1 ≤ K^2:=Nat.one_le_pow _ _ positive
  have positiveCap : 1 ≤ cap := by dsimp only [cap];omega
  have old:=Executable.importPrefix_encoded_polynomial pool nodes index
  have next:=Executable.importPrefix_encoded_polynomial pool nodes (index+1)
  have base : ((Encoding.array Encoding.node).encode pool).length+
      ((Encoding.list Encoding.node).encode nodes).length+1 ≤ K := by dsimp only [K];omega
  have power:=Nat.pow_le_pow_left base 2
  have oldPool : ((Encoding.array Encoding.node).encode state.1).length ≤ cap := by
    exact old.1.trans (Nat.mul_le_mul_left 20 power)
  have oldMapping : ((Encoding.array Encoding.natural).encode state.2).length ≤ cap := by
    have bound:=old.2.trans (Nat.mul_le_mul_left 10 power)
    change ((Encoding.array Encoding.natural).encode state.2).length ≤ 10*K^2 at bound
    change _ ≤ 20*K^2
    omega
  have successor : Executable.importPrefixState pool nodes (index+1)=
      Executable.importStep state nodes[index] := by
    simp only [Executable.importPrefixState,List.take_succ_eq_append_getElem inside,List.foldl_append,
      List.foldl_cons,List.foldl_nil]
    rfl
  have nextPool : ((Encoding.array Encoding.node).encode
      (Executable.intern state.1 (Executable.referenceMap state.2 nodes[index])).1).length ≤ cap := by
    simpa only [successor,Executable.importStep] using next.1.trans (Nat.mul_le_mul_left 20 power)
  have nextMapping : ((Encoding.array Encoding.natural).encode
      (state.2.push (Executable.intern state.1 (Executable.referenceMap state.2 nodes[index])).2)).length ≤ cap := by
    have bound:=next.2.trans (Nat.mul_le_mul_left 10 power)
    rw [successor] at bound
    change ((Encoding.array Encoding.natural).encode
      (state.2.push (Executable.intern state.1 (Executable.referenceMap state.2 nodes[index])).2)).length ≤ 10*K^2 at bound
    change _ ≤ 20*K^2
    omega
  have nodeSize : (Encoding.node.encode nodes[index]).length ≤
      ((Encoding.list Encoding.node).encode nodes).length := by
    simpa only [Encoding.array,Encoding.transport,List.toList_toArray] using
      Encoding.array_member_length_le Encoding.node nodes.toArray nodes[index]
        (by simpa only [List.toList_toArray] using List.getElem_mem inside)
  have nodeCap : (Encoding.node.encode nodes[index]).length ≤ cap := by
    dsimp only [K,cap] at *
    omega
  have sourceCap : sourceLength ≤ cap := by dsimp only [K,cap] at *;omega
  have bounded:=stepBudget_cap state.2 state.1 nodes[index] sourceLength cap positiveCap
    oldMapping oldPool nodeCap sourceCap nextPool nextMapping
  calc
    _ ≤ 100000000000000*cap^7 := bounded
    _ = importStepCoefficient*K^14 := by dsimp only [cap,importStepCoefficient];ring

end Counting.StackMachine.DagUpdate.Import
