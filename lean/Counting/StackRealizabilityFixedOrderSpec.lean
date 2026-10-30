import Counting.StackRealizabilityMachineSpec
import Counting.EncodingVerifier

namespace Counting.Encoding

/-- Fixed-order realization is a language of canonical binary inputs;
malformed encodings are negative instances. -/
def BinaryFixedOrderRealizable (input : List Bool) : Prop :=
  match fixedOrderInput.decodeExact input with
  | none => False
  | some (vista,ell,order) => vista.valid=true ∧ Realizability.Realizable ell order vista.denotes

def binaryFixedOrderVerifier (input witness : List Bool) : Bool :=
  match fixedOrderInput.decodeExact input,(list natural).decodeExact witness with
  | some (vista,ell,order),some counts => RealizabilityVerifier.verify vista counts.toArray ell order
  | _,_ => false

theorem binaryFixedOrder_bounded_witnesses (input : List Bool) :
    BinaryFixedOrderRealizable input ↔ ∃witness,
      witness.length≤3*(input.length+1)^2 ∧ binaryFixedOrderVerifier input witness=true := by
  cases decoded : fixedOrderInput.decodeExact input with
  | none => simp [BinaryFixedOrderRealizable,binaryFixedOrderVerifier,decoded]
  | some value =>
    obtain ⟨vista,ell,order⟩ := value
    have inputEq := (fixedOrderInput.decodeExact_iff _ _).mp decoded
    simp only [BinaryFixedOrderRealizable,decoded]
    constructor
    · intro possible
      obtain ⟨weights,accepted,bounded⟩ := exists_encoded_bounded_certificate vista possible.1 ell order possible.2
      refine ⟨(list natural).encode weights.toList,by simpa only [inputEq] using bounded,?_⟩
      have witnessDecoded := ((list natural).decodeExact_iff _ weights.toList).mpr rfl
      simp only [binaryFixedOrderVerifier,decoded,witnessDecoded,Array.toArray_toList,accepted]
    · rintro ⟨witness,_,accepted⟩
      cases parsed : (list natural).decodeExact witness with
      | none => simp [binaryFixedOrderVerifier,decoded,parsed] at accepted
      | some counts =>
        have verified : RealizabilityVerifier.verify vista counts.toArray ell order=true := by
          simpa only [binaryFixedOrderVerifier,decoded,parsed] using accepted
        exact ⟨((RealizabilityVerifier.verify_iff_certificate vista counts.toArray ell order).mp verified).1,
          RealizabilityVerifier.verify_sound vista counts.toArray ell order verified⟩

end Counting.Encoding
