import Counting.HardnessNetworkMachineInputSpec

namespace Counting.HardnessNetworkMachine
set_option backward.isDefEq.respectTransparency false

theorem list_encode_map {α β : Type} (source : Encoding.Codec α) (target : Encoding.Codec β)
    (f : α→β) (same : ∀ a,target.encode (f a)=source.encode a) (values : List α) :
    (Encoding.list target).encode (values.map f)=(Encoding.list source).encode values := by
  simp only [Encoding.list,List.length_map]
  congr 1
  induction values with
  | nil=>rfl
  | cons a rest ih=>simp only [List.map_cons,Encoding.sequence,same,ih]

theorem array_encode_toArray {α : Type} (codec : Encoding.Codec α) (values : List α) :
    (Encoding.array codec).encode values.toArray=(Encoding.list codec).encode values := by
  simp [Encoding.array,Encoding.transport]

theorem matrix_encode_toArray (matrix : List (List Nat)) :
    (Encoding.array (Encoding.array Encoding.natural)).encode (matrix.map List.toArray).toArray=
      (Encoding.list (Encoding.list Encoding.natural)).encode matrix := by
  rw [array_encode_toArray]
  exact list_encode_map _ _ _ (array_encode_toArray Encoding.natural) matrix

def networkWord (base : Nat) (coefficients : List Nat) : List Bool :=
  (Encoding.list Encoding.boolean).encode (networkLeaders base coefficients)++
    (Encoding.list (Encoding.list (Encoding.list Encoding.natural))).encode (networkRounds base coefficients)

theorem networkWord_data (base : Nat) (coefficients : List Nat) :
    networkWord base coefficients=Encoding.networkInput.encode (networkData base coefficients) := by
  simp only [networkWord,Encoding.networkInput,Encoding.transport,Encoding.product,networkData]
  rw [array_encode_toArray,array_encode_toArray]
  congr 1
  exact (list_encode_map _ _ _ matrix_encode_toArray _).symm

/-- Exact equality of the full binary network serialization, including
agent markers, all matrix/row headers and every binary arc multiplicity. -/
theorem networkWord_actual {q m : Nat} (inst : X3C.Instance q m) :
    networkWord (X3C.base q) (coefficientTable inst)=HardnessEncoded.networkBits inst := by
  rw [networkWord_data,networkData_actual]
  rfl

theorem networkWord_coefficients {q m : Nat} (inst : X3C.Instance q m) :
    networkWord (X3C.base q) (External.CoefficientMachine.inputCoefficients
      ⟨q,m,⟨inst.triples,inst.triple_card⟩⟩)=HardnessEncoded.networkBits inst := by
  rw [←coefficientTable_actual]
  exact networkWord_actual inst

end Counting.HardnessNetworkMachine
