import Counting.StackRationalPredicates

namespace Counting.StackMachine.RationalArithmetic.Predicates

theorem bits_empty (n : Nat) : n.bits.isEmpty = decide (n=0) := by
  have empty : n.bits=[] ↔ n=0 := by
    constructor
    · intro equal
      exact Encoding.bits_injective (show n.bits=Nat.bits 0 from equal)
    · rintro rfl; rfl
  apply Bool.eq_iff_iff.mpr
  simp [empty]

theorem canonical_predicate (kind : Kind) (value : Rat) :
    predicate kind (Encoding.rational.encode value) =
      check kind value.num.natAbs.bits value.den.bits (Encoding.negative value.num) := by
  have parsed := Pair.parsed_rational value []
  have signed := Pair.sign_rational value []
  simp only [List.append_nil] at parsed signed
  simp only [predicate,parsed,signed]

theorem zero_correct (value : Rat) : predicate .zero (Encoding.rational.encode value) = decide (value=0) := by
  rw [canonical_predicate]
  simp only [check,bits_empty,Int.natAbs_eq_zero,Rat.num_eq_zero]

theorem negative_correct (value : Rat) : predicate .negative (Encoding.rational.encode value) = decide (value<0) := by
  rw [canonical_predicate]
  simp only [check,Encoding.negative,Rat.num_neg]

theorem positive_correct (value : Rat) : predicate .positive (Encoding.rational.encode value) = decide (0<value) := by
  rw [canonical_predicate]
  simp only [check,Encoding.negative,bits_empty]
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.and_eq_true,Bool.not_eq_true',decide_eq_false_iff_not,not_lt,
    Int.natAbs_eq_zero,decide_eq_true_eq]
  rw [← Rat.num_pos]
  omega

theorem integral_correct (value : Rat) : predicate .integral (Encoding.rational.encode value) = decide (value.den=1) := by
  rw [canonical_predicate]
  change (value.den.bits == Nat.bits 1) = _
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq,decide_eq_true_eq,Encoding.bits_injective.eq_iff]

end Counting.StackMachine.RationalArithmetic.Predicates
