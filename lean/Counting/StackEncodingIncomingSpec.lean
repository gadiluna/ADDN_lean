import Counting.StackEncodingPairSemantics
import Counting.StackBinaryCompareBits
import Counting.DagSemanticsValidityNodes

/-! The incoming-edge predicate is a graph check, separate from canonical
serialization. It checks positive multiplicities, sorted distinct references,
and the reference bound; it does not check levels or causal closure. -/
namespace Counting.StackMachine.EncodingPrograms

 def incomingCheck (bound : Nat) (previous : Option Nat) : List (Nat × Nat) → Bool
  | [] => true
  | (index,count)::rest => decide (0<count) && decide (index<bound) &&
      previous.all (fun p=>decide (p< index)) && incomingCheck bound (some index) rest

theorem incomingCheck_cons (bound index count : Nat) (previous : Option Nat) (rest : List (Nat × Nat)) :
    incomingCheck bound previous ((index,count)::rest)=true ↔
      0<count ∧ index<bound ∧ (∀ p∈previous,p< index) ∧ incomingCheck bound (some index) rest=true := by
  simp only [incomingCheck,Bool.and_eq_true,decide_eq_true_eq,Option.all_eq_true]
  tauto

theorem incomingCheck_previous (bound : Nat) (previous : Option Nat) (edges : List (Nat × Nat)) :
    incomingCheck bound previous edges=true ↔
      incomingCheck bound none edges=true ∧ ∀ edge∈edges.head?,∀ p∈previous,p<edge.1 := by
  cases edges with
  | nil => simp [incomingCheck]
  | cons edge rest => rcases edge with ⟨i,c⟩; simp only [incomingCheck_cons,List.head?_cons,Option.mem_some_iff]; simp; tauto

theorem incomingCheck_iff (bound : Nat) (edges : List (Nat × Nat)) :
    incomingCheck bound none edges=true ↔ Executable.countsSorted edges=true ∧
      edges.all (fun edge=>decide (edge.1<bound))=true := by
  induction edges with
  | nil => simp [incomingCheck,Executable.countsSorted]
  | cons edge rest ih =>
      rcases edge with ⟨i,c⟩
      rw [incomingCheck_cons,incomingCheck_previous,ih]
      simp only [Option.not_mem_none,Executable.countsSorted,Bool.and_eq_true,
        decide_eq_true_eq,List.all_cons,Option.mem_some_iff]
      cases rest with
      | nil => simp; tauto
      | cons edge rest => simp; tauto

/-- The item machine works directly on payloads; canonicality is checked
separately and not inferred from the numeric comparison. -/
def incomingPayloadCheck (bound previous : List Bool) (first : Bool) (parsed : PairParseResult) : Bool :=
  parsed.accepted && canonicalPayload parsed.first && lastPayloadBit false parsed.second &&
    !Binary.compareBits true bound parsed.first &&
    (first || !Binary.compareBits true parsed.first previous)

theorem positivePayload_iff (bits : List Bool) :
    lastPayloadBit false bits=true ↔ canonicalPayload bits=true ∧ 0<Encoding.value bits := by
  cases bits with
  | nil => simp [lastPayloadBit,canonicalPayload,Encoding.value]
  | cons bit bits =>
      have canon : lastPayloadBit false (bit::bits)=canonicalPayload (bit::bits) := rfl
      rw [canon]
      constructor
      · intro h
        refine ⟨h,?_⟩
        have canonical := (canonicalPayload_iff _).mp h
        by_contra zero
        have z : Encoding.value (bit::bits)=0 := by omega
        rw [z] at canonical
        simp at canonical
      · exact And.left

theorem incomingPayloadCheck_iff (bound previous : List Bool) (first : Bool) (parsed : PairParseResult) :
    incomingPayloadCheck bound previous first parsed=true ↔
      parsed.accepted=true ∧ parsed.first=(Encoding.value parsed.first).bits ∧
      parsed.second=(Encoding.value parsed.second).bits ∧ 0<Encoding.value parsed.second ∧
      Encoding.value parsed.first<Encoding.value bound ∧
      (first=true ∨ Encoding.value previous<Encoding.value parsed.first) := by
  have neg (a b : List Bool) : (!Binary.compareBits true a b)=true ↔ Encoding.value b<Encoding.value a := by
    have comparison:=Binary.compareBits_le a b
    cases h : Binary.compareBits true a b <;> simp_all
  simp only [incomingPayloadCheck,Bool.and_eq_true,Bool.or_eq_true,positivePayload_iff,
    canonicalPayload_iff,neg]
  tauto

end Counting.StackMachine.EncodingPrograms
