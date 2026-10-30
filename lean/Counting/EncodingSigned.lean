import Counting.EncodingBinary
import Mathlib.Data.Rat.Defs

/-! Canonical binary formats for exact signed and rational arithmetic.
The sign bit precedes the framed magnitude; zero always has a false sign.
Rationals encode their reduced integer numerator and positive denominator.
Prefix decoding is totalized by `mkRat`; exact decoding checks canonicality. -/
namespace Counting.Encoding

def signedValue (negative : Bool) (magnitude : Nat) : Int :=
  if negative then -(magnitude : Int) else (magnitude : Int)

def negative (value : Int) : Bool := decide (value < 0)

@[simp] theorem signedValue_negative_natAbs (value : Int) :
    signedValue (negative value) value.natAbs = value := by
  by_cases below : value < 0
  · simp only [signedValue,negative,decide_eq_true below,ite_true]
    rw [Int.ofNat_natAbs_of_nonpos (le_of_lt below),neg_neg]
  · simp only [signedValue,negative,decide_eq_false below,Bool.false_eq_true,ite_false]
    exact Int.natAbs_of_nonneg (le_of_not_gt below)

def integer : Codec Int := transport (product boolean natural)
  (fun value => (negative value,value.natAbs))
  (fun pair => signedValue pair.1 pair.2) signedValue_negative_natAbs

theorem integer_encode (value : Int) :
    integer.encode value = negative value :: natural.encode value.natAbs := rfl

@[simp] theorem integer_length (value : Int) :
    (integer.encode value).length = 2*value.natAbs.size+2 := by
  rw [integer_encode,List.length_cons,natural_length]

def rational : Codec Rat := transport (product integer natural)
  (fun value => (value.num,value.den))
  (fun pair => mkRat pair.1 pair.2) Rat.mkRat_self

theorem rational_encode (value : Rat) :
    rational.encode value = integer.encode value.num ++ natural.encode value.den := rfl

@[simp] theorem rational_length (value : Rat) :
    (rational.encode value).length = 2*(value.num.natAbs.size+value.den.size)+3 := by
  rw [rational_encode,List.length_append,integer_length,natural_length]
  omega

theorem integer_injective : Function.Injective integer.encode := integer.injective
theorem rational_injective : Function.Injective rational.encode := rational.injective

end Counting.Encoding
