import Counting.StackEncodingParserProduct

namespace Counting.StackMachine.EncodingPrograms

set_option backward.isDefEq.respectTransparency false

def naturalEffect (input : List Bool) : ParseEffect :=
  ⟨unframeSuffix input,Encoding.frame (unframePayload input),itemAccepted input⟩

/-- The atom uses the already verified unframing, canonicality, reframing,
and reversal instructions; failed fields still restore all temporary stacks. -/
def naturalParser (extra : Nat) (w : ListWorkspace extra) :
    VerifiedParser (extra+6) (w 0) (w 3) (w 6) Nat Encoding.natural where
  work := {w 1,w 2,w 4,w 5}
  separate r member := by
    simp only [Finset.mem_insert,Finset.mem_singleton] at member
    rcases member with rfl|rfl|rfl|rfl <;> simp [w.injective.eq_iff]
  routine := listItem extra w
  effect := naturalEffect
  coefficient := 40
  exponent := 1
  suffix_le := unframe_suffix_length
  code_le input := by
    have payload:=unframe_payload_length input
    simp only [naturalEffect,Encoding.frame_length,Complexity.polynomial,pow_one]
    omega
  sound input accepted := by
    obtain ⟨split,code⟩:=itemAccepted_sound input accepted
    exact ⟨Encoding.value (unframePayload input),split.symm,code⟩
  roundtrip value suffix := by
    have canonical : canonicalPayload value.bits=true := (canonicalPayload_iff value.bits).mpr (by rw [Encoding.value_bits])
    have parsed : Encoding.unframe (Encoding.natural.encode value++suffix)=some (value.bits,suffix) := Encoding.unframe_frame _ _
    simp only [naturalEffect,unframeSuffix,unframePayload,itemAccepted,parsed,Option.map_some,Option.getD_some,
      Option.isSome_some,canonical,Bool.true_and]
    rfl
  executes store accepted tail status empty := by
    obtain ⟨time,bound,ran⟩:=listItem_executes extra w store accepted tail status
      (empty (w 1) (by simp)) (empty (w 2) (by simp)) (empty (w 4) (by simp)) (empty (w 5) (by simp))
    have result : listItemResult extra w store accepted tail=
        parseStore (w 0) (w 3) (w 6) store accepted tail (naturalEffect (store (w 0))) := by
      funext r
      by_cases a : r=w 0
      · subst r; simp [listItemResult,parseStore,naturalEffect,w.injective.eq_iff]
      · by_cases b : r=w 3
        · subst r; simp [listItemResult,parseStore,naturalEffect,w.injective.eq_iff]
        · by_cases c : r=w 6
          · subst r; simp [listItemResult,parseStore,naturalEffect,w.injective.eq_iff]
          · simp [listItemResult,parseStore,a,b,c]
    rw [result] at ran
    exact ⟨time,by simpa only [Complexity.polynomial,pow_one] using (show time≤40*((store (w 0)).length+1) by omega),ran⟩

end Counting.StackMachine.EncodingPrograms
