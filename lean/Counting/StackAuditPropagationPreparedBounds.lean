import Counting.StackAuditPropagationPrepared

namespace Counting.StackMachine.AuditPropagation

/-- A single explicit polynomial in the actual serialized input controls
anchor assignment and every backward pass, including all intermediate arrays. -/
theorem preparedBudget_polynomial (anchor : Nat) (vista : Executable.Vista) (values : Array Nat)
    (fits : anchor ≤ vista.nodes.size) :
    preparedBudget anchor vista values ≤
      100000000000000000000000000000000000000000000000000*
        ((propagationInputWord anchor vista values).length+1)^32 := by
  let L:=(propagationInputWord anchor vista values).length
  let S:=L+1
  let table:=(Encoding.sequence Encoding.node vista.nodes.toList++Encoding.natural.encode vista.bottom).length
  let code:=(Encoding.vista.encode vista).length
  let zeros:=((Encoding.array Encoding.natural).encode (Array.replicate vista.nodes.size 0)).length
  let stream:=(Encoding.sequence Encoding.natural values.toList).length
  let assignedLength:=((Encoding.array Encoding.natural).encode (assigned vista anchor values)).length
  let width:=5*(assignedLength+1)^3
  have positive : 1 ≤ S := by dsimp only [S];omega
  have inputLength : L=2*anchor.size+1+(2*code+1)+
      (2*values.size.size+1)+stream := by
    simp only [L,propagationInputWord,propagationInputCodec,Encoding.product,Encoding.framed,
      List.length_append,Encoding.natural_length,Encoding.frame_length,Encoding.array,
      Encoding.transport,Encoding.list,Array.length_toList,code,stream]
    omega
  have codeBound : code ≤ S := by dsimp only [S];omega
  have streamBound : stream ≤ S := by dsimp only [S];omega
  have nodeBound : vista.nodes.size ≤ S := (Encoding.vista_nodes_le_length vista).trans codeBound
  have anchorBound : anchor ≤ S := fits.trans nodeBound
  have bitsBound : anchor.size ≤ S := (Nat.size_le.mpr Nat.lt_two_pow_self).trans anchorBound
  have tableBound : table ≤ S := by
    have split : code=(Encoding.natural.encode vista.nodes.size).length+table := by
      simp only [code,table,Encoding.vista,Encoding.transport,Encoding.product,
        Encoding.list,List.length_append,Array.length_toList]
      omega
    omega
  have zeroLength : zeros=2*vista.nodes.size.size+1+vista.nodes.size := by
    simp only [zeros,zero_array_word,List.length_append,Encoding.natural_length,List.length_replicate]
  have countBits : vista.nodes.size.size ≤ vista.nodes.size := Nat.size_le.mpr Nat.lt_two_pow_self
  have zeroBound : zeros ≤ 4*S := by omega
  have assignedBound : assignedLength ≤ 5*S := by
    have assignedSize:=assigned_encoded_length vista anchor values
    change assignedLength ≤ zeros+stream at assignedSize
    omega
  have widthBound : width ≤ 1080*S^3 := by
    have powered:=Nat.pow_le_pow_left (by omega : assignedLength+1 ≤ 6*S) 3
    dsimp only [width]
    nlinarith only [powered]
  have oneCube : 1 ≤ S^3 := Nat.one_le_pow _ _ positive
  have nextWidth : width+1 ≤ 1081*S^3 := by omega
  have square:=Nat.pow_le_pow_left nextWidth 2
  have s6 : S ≤ S^6 := Nat.le_self_pow (by decide) _
  have one6 : 1 ≤ S^6 := Nat.one_le_pow _ _ positive
  have inner : table+code+8*(width+1)^2+3*vista.nodes.size+3 ≤ 10000000*S^6 := by
    have exactSquare : (1081*S^3)^2=1168561*S^6 := by ring
    rw [exactSquare] at square
    nlinarith only [square,tableBound,codeBound,nodeBound,s6,one6]
  have powered:=Nat.pow_le_pow_left inner 5
  have initial : table+zeros+stream+anchor.size+vista.nodes.size+1 ≤ 9*S := by omega
  have initialPower:=Nat.pow_le_pow_left initial 4
  have anchorPart:=Nat.mul_le_mul nodeBound
    (Nat.add_le_add_right (Nat.mul_le_mul_left 9000 initialPower) 2)
  have innerPart:=Nat.mul_le_mul nodeBound
    (Nat.add_le_add_right (Nat.mul_le_mul_left 30000 powered) 2)
  have uniform : downUniform vista table width ≤
      S*(30000*(10000000*S^6)^5+2)+1+80*(S+1) := by
    unfold downUniform
    change vista.nodes.size*(30000*(table+code+8*(width+1)^2+3*vista.nodes.size+3)^5+2)+1+
      80*(vista.nodes.size+1) ≤ _
    omega
  have downPart:=Nat.mul_le_mul anchorBound (Nat.add_le_add_right uniform 2)
  have result : preparedBudget anchor vista values ≤
      S*(9000*(9*S)^4+2)+1+6*S+S+6*S+6*S+16+
        S*(S*(30000*(10000000*S^6)^5+2)+1+80*(S+1)+2)+1+2 := by
    unfold preparedBudget
    change vista.nodes.size*(9000*(table+zeros+stream+anchor.size+vista.nodes.size+1)^4+2)+1+
      6*vista.nodes.size+stream+6*anchor.size+6*anchor+16+
      (anchor*(downUniform vista table width+2)+1)+2 ≤ _
    omega
  have p5 : S^5 ≤ S^32 := Nat.pow_le_pow_right positive (by decide)
  have p2 : S^2 ≤ S^32 := Nat.pow_le_pow_right positive (by decide)
  have p1 : S ≤ S^32 := Nat.le_self_pow (by decide) _
  have p0 : 1 ≤ S^32 := Nat.one_le_pow _ _ positive
  change preparedBudget anchor vista values ≤ 100000000000000000000000000000000000000000000000000*S^32
  nlinarith only [result,p5,p2,p1,p0]

end Counting.StackMachine.AuditPropagation
