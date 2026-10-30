import Counting.StackRationalPair

namespace Counting.StackMachine.RationalArithmetic.Pair

def firstValue (input : List Bool) : Rat := mkRat
  (Encoding.signedValue (firstSign input) (Encoding.value (first input).first))
  (Encoding.value (first input).second)
def secondValue (input : List Bool) : Rat := mkRat
  (Encoding.signedValue (secondSign input) (Encoding.value (second input).first))
  (Encoding.value (second input).second)

theorem parsed_rational (value : Rat) (suffix : List Bool) :
    parsed (Encoding.rational.encode value++suffix) =
      ⟨value.num.natAbs.bits,value.den.bits,suffix,true⟩ := by
  simp only [Encoding.rational_encode,Encoding.integer_encode,List.cons_append,
    parsed,List.tail_cons,Encoding.natural,EncodingPrograms.parsePair_frames]

theorem sign_rational (value : Rat) (suffix : List Bool) :
    parsedSign (Encoding.rational.encode value++suffix) = Encoding.negative value.num := by
  simp only [Encoding.rational_encode,Encoding.integer_encode,List.cons_append,
    parsedSign,List.headD_cons]

theorem first_rationals (a b : Rat) :
    first ((Encoding.product Encoding.rational Encoding.rational).encode (a,b)) =
      ⟨a.num.natAbs.bits,a.den.bits,Encoding.rational.encode b,true⟩ :=
  parsed_rational a (Encoding.rational.encode b)

theorem second_rationals (a b : Rat) :
    second ((Encoding.product Encoding.rational Encoding.rational).encode (a,b)) =
      ⟨b.num.natAbs.bits,b.den.bits,[],true⟩ := by
  change parsed (first ((Encoding.product Encoding.rational Encoding.rational).encode (a,b))).suffix = _
  rw [first_rationals]
  simpa only [List.append_nil] using parsed_rational b []

theorem firstSign_rationals (a b : Rat) :
    firstSign ((Encoding.product Encoding.rational Encoding.rational).encode (a,b)) = Encoding.negative a.num :=
  sign_rational a (Encoding.rational.encode b)

theorem secondSign_rationals (a b : Rat) :
    secondSign ((Encoding.product Encoding.rational Encoding.rational).encode (a,b)) = Encoding.negative b.num := by
  change parsedSign (first ((Encoding.product Encoding.rational Encoding.rational).encode (a,b))).suffix = _
  rw [first_rationals]
  simpa only [List.append_nil] using sign_rational b []

theorem values_rationals (a b : Rat) :
    firstValue ((Encoding.product Encoding.rational Encoding.rational).encode (a,b)) = a ∧
    secondValue ((Encoding.product Encoding.rational Encoding.rational).encode (a,b)) = b := by
  simp only [firstValue,secondValue,first_rationals,second_rationals,firstSign_rationals,secondSign_rationals,
    Encoding.value_bits,Encoding.signedValue_negative_natAbs,Rat.mkRat_self,and_self]

end Counting.StackMachine.RationalArithmetic.Pair
