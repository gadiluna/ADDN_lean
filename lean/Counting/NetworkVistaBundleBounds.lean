import Counting.NetworkVistaBundleValues

namespace Counting.StackMachine.NetworkVista

/-- Each retained bundle uses a view serialization and one natural that
already occurs in its explicit matrix row. The bound also covers a receiver
outside a malformed row: that default-zero edge contributes no message. -/
theorem receivedPairs_code_length_le (receiver:Nat) (pairs:List (Executable.Vista×Array Nat)) :
    (Encoding.sequence (Encoding.product Encoding.vista Encoding.natural) (receivedPairs receiver pairs)).length≤
      (Encoding.sequence Encoding.vista (pairs.map Prod.fst)).length+
      (Encoding.sequence (Encoding.array Encoding.natural) (pairs.map Prod.snd)).length := by
  induction pairs with
  | nil=>rfl
  | cons pair pairs ih=>
    obtain ⟨vista,row⟩:=pair
    by_cases zero:row[receiver]?.getD 0=0
    · simp only [receivedPairs,if_pos zero,List.map_cons,Encoding.sequence,List.length_append]
      omega
    · have member:row[receiver]?.getD 0∈row.toList:=by
        cases lookup:row[receiver]? with
        | none=>simp [lookup] at zero
        | some amount=>
          simpa only [lookup,Option.getD_some,Array.mem_toList_iff] using Array.mem_of_getElem? lookup
      have codeBound:=Encoding.array_member_length_le Encoding.natural row (row[receiver]?.getD 0) member
      have productLength:((Encoding.product Encoding.vista Encoding.natural).encode (vista,row[receiver]?.getD 0)).length=
          (Encoding.vista.encode vista).length+(Encoding.natural.encode (row[receiver]?.getD 0)).length:=by
        simp only [Encoding.product,List.length_append]
      simp only [receivedPairs,if_neg zero,List.map_cons,Encoding.sequence,List.length_append,productLength]
      omega

end Counting.StackMachine.NetworkVista
