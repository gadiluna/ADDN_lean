import Counting.HardnessEncodedBounds
import Counting.HardnessEncodedRealization
import Counting.X3CEncoding

/-! Total binary reductions from the complement of explicitly encoded X3C.
Malformed source words are negative X3C instances, hence must map to positive
recognition instances. The fallback is itself a valid baseline construction.
These functional and size results support the complete machine reductions. -/
namespace Counting.HardnessEncoded
open Encoding

def fallback : X3C.Instance 2 0 where
  triples := Fin.elim0
  triple_card := by intro j; exact Fin.elim0 j
  distinct := by intro a; exact Fin.elim0 a

theorem fallback_no_cover : ¬ ∃ chosen, fallback.IsExactCover chosen := by
  intro ⟨chosen, cover⟩
  have empty : chosen = ∅ := Finset.eq_empty_of_forall_notMem (fun a => Fin.elim0 a)
  have impossible := cover (0 : Fin 6)
  simp only [empty, Finset.filter_empty, Finset.card_empty] at impossible
  omega

def networkReduce (word : List Bool) : List Bool :=
  match X3CEncoding.codec.decodeExact word with
  | none => networkBits fallback
  | some source => networkBits source.2.2.normalize

def vistaReduce (word : List Bool) : List Bool :=
  match X3CEncoding.codec.decodeExact word with
  | none => vistaBits fallback
  | some source => vistaBits source.2.2.normalize

theorem decoded_x3c_iff (word : List Bool) (source : X3CEncoding.Input)
    (parsed : X3CEncoding.codec.decodeExact word = some source) :
    X3CEncoding.BinaryX3C word ↔ ∃ chosen, source.2.2.IsExactCover chosen := by
  rw [← (X3CEncoding.decodeExact_iff word source).mp parsed]
  exact X3CEncoding.encoded_yes_iff source

theorem networkReduce_correct (word : List Bool) :
    BinarySomeAgentKnows (networkReduce word) ↔ ¬ X3CEncoding.BinaryX3C word := by
  cases parsed : X3CEncoding.codec.decodeExact word with
  | none =>
      simp only [networkReduce, parsed]
      rw [networkBits_correct fallback (by omega)]
      exact iff_of_true fallback_no_cover (X3CEncoding.invalid_negative word parsed)
  | some source =>
      simp only [networkReduce, parsed]
      exact (networkBits_correct source.2.2.normalize (by omega)).trans
        (not_congr (source.2.2.normalize_exactCover_iff.trans (decoded_x3c_iff word source parsed).symm))

theorem vistaReduce_correct (word : List Bool) :
    BinaryAtMostOneVista (vistaReduce word) ↔ ¬ X3CEncoding.BinaryX3C word := by
  cases parsed : X3CEncoding.codec.decodeExact word with
  | none =>
      simp only [vistaReduce, parsed]
      rw [vistaBits_correct fallback (by omega)]
      exact iff_of_true fallback_no_cover (X3CEncoding.invalid_negative word parsed)
  | some source =>
      simp only [vistaReduce, parsed]
      exact (vistaBits_correct source.2.2.normalize (by omega)).trans
        (not_congr (source.2.2.normalize_exactCover_iff.trans (decoded_x3c_iff word source parsed).symm))

def networkReductionSizeConstant : Nat :=
  max (networkBits fallback).length (networkSizeConstant*3^8)

def vistaReductionSizeConstant : Nat :=
  max (vistaBits fallback).length (vistaSizeConstant*3^40)

theorem shifted_power_bound (L exponent : Nat) : (L+3)^exponent ≤ 3^exponent*(L+1)^exponent := by
  simpa only [mul_pow] using Nat.pow_le_pow_left (show L+3 ≤ 3*(L+1) by omega) exponent

theorem networkReduce_length (word : List Bool) :
    (networkReduce word).length ≤ networkReductionSizeConstant*(word.length+1)^8 := by
  have positive : 1 ≤ (word.length+1)^8 := Nat.one_le_pow 8 _ (by omega)
  cases parsed : X3CEncoding.codec.decodeExact word with
  | none =>
      simp only [networkReduce, parsed]
      calc
        _ = (networkBits fallback).length*1 := by omega
        _ ≤ (networkBits fallback).length*(word.length+1)^8 := Nat.mul_le_mul_left _ positive
        _ ≤ _ := Nat.mul_le_mul_right _ (le_max_left _ _)
  | some source =>
      obtain ⟨elements, triples⟩ := X3CEncoding.decoded_input_size_bounds word source parsed
      have kept := source.2.2.kept_card_le
      have bound := networkBits_length_polynomial source.2.2.normalize (by omega) (word.length+2)
        (by omega) (by omega)
      have shift := Nat.mul_le_mul_left networkSizeConstant (shifted_power_bound word.length 8)
      simp only [networkReduce, parsed]
      calc
        _ ≤ networkSizeConstant*(word.length+2+1)^8 := bound
        _ ≤ (networkSizeConstant*3^8)*(word.length+1)^8 := by
          simpa only [Nat.add_assoc, Nat.reduceAdd, Nat.mul_assoc] using shift
        _ ≤ _ := Nat.mul_le_mul_right _ (le_max_right _ _)

theorem vistaReduce_length (word : List Bool) :
    (vistaReduce word).length ≤ vistaReductionSizeConstant*(word.length+1)^40 := by
  have positive : 1 ≤ (word.length+1)^40 := Nat.one_le_pow 40 _ (by omega)
  cases parsed : X3CEncoding.codec.decodeExact word with
  | none =>
      simp only [vistaReduce, parsed]
      calc
        _ = (vistaBits fallback).length*1 := by omega
        _ ≤ (vistaBits fallback).length*(word.length+1)^40 := Nat.mul_le_mul_left _ positive
        _ ≤ _ := Nat.mul_le_mul_right _ (le_max_left _ _)
  | some source =>
      obtain ⟨elements, triples⟩ := X3CEncoding.decoded_input_size_bounds word source parsed
      have kept := source.2.2.kept_card_le
      have bound := vistaBits_length_polynomial source.2.2.normalize (by omega) (word.length+2)
        (by omega) (by omega)
      have shift := Nat.mul_le_mul_left vistaSizeConstant (shifted_power_bound word.length 40)
      simp only [vistaReduce, parsed]
      calc
        _ ≤ vistaSizeConstant*(word.length+2+1)^40 := bound
        _ ≤ (vistaSizeConstant*3^40)*(word.length+1)^40 := by
          simpa only [Nat.add_assoc, Nat.reduceAdd, Nat.mul_assoc] using shift
        _ ≤ _ := Nat.mul_le_mul_right _ (le_max_right _ _)

theorem networkReduce_restricted (word : List Bool) :
    ∃ target, decodeNetwork? (networkReduce word) = some target ∧
      inputLeaderCount target = 1 ∧ ∀ r, 0 < r → r ≤ target.rounds.size →
        ∀ agent : InputAgent target, inputGraph target r agent agent = 0 := by
  have restricted {q m : Nat} (inst : X3C.Instance q m) (large : 2 ≤ q) :
      ∃ target, decodeNetwork? (networkBits inst) = some target ∧ inputLeaderCount target = 1 ∧
        ∀ r, 0 < r → r ≤ target.rounds.size → ∀ agent : InputAgent target,
          inputGraph target r agent agent = 0 := by
    refine ⟨input inst, (decodeNetwork_iff _ _).mpr ⟨rfl, input_valid inst large⟩,
      input_leaderCount inst, ?_⟩
    intro r positive within agent
    rw [input_rounds] at within
    exact input_loopless inst r positive within agent
  cases parsed : X3CEncoding.codec.decodeExact word with
  | none => simpa only [networkReduce, parsed] using restricted fallback (by omega)
  | some source => simpa only [networkReduce, parsed] using restricted source.2.2.normalize (by omega)

theorem vistaReduce_restricted (word : List Bool) :
    ∃ view order, vistaInput.decodeExact (vistaReduce word) = some (view,1) ∧
      view.valid = true ∧ Realizability.Realizable 1 order view.denotes := by
  have restricted {q m : Nat} (inst : X3C.Instance q m) (large : 2 ≤ q) :
      ∃ view order, vistaInput.decodeExact (vistaBits inst) = some (view,1) ∧
        view.valid = true ∧ Realizability.Realizable 1 order view.denotes :=
    ⟨leaderVista inst, X3C.baselineMass q m+1, (vistaInput.decodeExact_iff _ _).mpr rfl,
      leaderVista_valid inst, leaderVista_realizable inst large⟩
  cases parsed : X3CEncoding.codec.decodeExact word with
  | none => simpa only [vistaReduce, parsed] using restricted fallback (by omega)
  | some source => simpa only [vistaReduce, parsed] using restricted source.2.2.normalize (by omega)

end Counting.HardnessEncoded
