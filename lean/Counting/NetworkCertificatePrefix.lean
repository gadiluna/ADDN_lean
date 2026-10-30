import Counting.NetworkCertificateLanguage

namespace Counting.NetworkCertificate
open Encoding

theorem product_decodeExact_prefix {A B : Type} (first : Codec A) (second : Codec B)
    (a : A) (bits : List Bool) :
    (product first second).decodeExact (first.encode a++bits)=
      (second.decodeExact bits).map (fun b=>(a,b)) := by
  unfold Codec.decodeExact
  simp only [product,first.roundtrip,bind,Option.bind_some]
  cases decoded : second.decode bits with
  | none => rfl
  | some pair =>
    rcases pair with ⟨b,suffix⟩
    simp only [pure,Option.bind_some,List.append_cancel_left_eq]
    split <;> rfl

def inputWord (ell : Nat) (views : Array Executable.Vista) (witness : List Bool) : List Bool :=
  natural.encode ell++(array vista).encode views++witness

theorem predicate_inputWord (ell : Nat) (views : Array Executable.Vista) (witness : List Bool) :
    predicate (inputWord ell views witness)=
      match networkWitness.decodeExact witness with
      | none=>false
      | some certificates=>check ell views.toList certificates := by
  unfold predicate inputWord
  change (match (product natural (product (list vista) networkWitness)).decodeExact
    (natural.encode ell++(list vista).encode views.toList++witness) with
    |none=>false|some input=>check input.1 input.2.1 input.2.2)=_
  rw [List.append_assoc,product_decodeExact_prefix,product_decodeExact_prefix]
  cases networkWitness.decodeExact witness <;> rfl

theorem predicate_raw_inputWord (input : Simulation.Input) (witness : List Bool)
    (valid : networkValid input=true) :
    predicate (inputWord (inputLeaderCount input) (rawInputVistas input) witness)=
      binaryRawNetworkComplementVerifier (networkInput.encode input) witness := by
  rw [predicate_inputWord,binaryRawNetworkComplementVerifier,
    (decodeNetwork_iff _ _).mpr ⟨rfl,valid⟩]
  cases networkWitness.decodeExact witness <;> rfl

end Counting.NetworkCertificate
