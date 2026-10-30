import Counting.StackArithmeticBits

namespace Counting.StackMachine.Binary

/-- One column of binary subtraction, with its incoming borrow. -/
def differenceBit (borrow a b : Bool) : Bool := xor (xor a b) borrow

def borrowBit (borrow a b : Bool) : Bool := (!a && (b || borrow)) || (b && borrow)

theorem fullSubtractor (borrow a b : Bool) :
    (if a then 1 else 0) + 2*(if borrowBit borrow a b then 1 else 0) =
      (if b then 1 else 0) + (if borrow then 1 else 0) + (if differenceBit borrow a b then 1 else 0) := by
  cases borrow <;> cases a <;> cases b <;> decide

/-- Fixed-width subtraction returns all result columns and the final
borrow. The caller may inspect the borrow before normalizing the digits. -/
def subtractBits (borrow : Bool) : List Bool → List Bool → List Bool × Bool
  | [], [] => ([],borrow)
  | a::as, [] =>
      let tail := subtractBits (borrowBit borrow a false) as []
      (differenceBit borrow a false::tail.1,tail.2)
  | [], b::bs =>
      let tail := subtractBits (borrowBit borrow false b) [] bs
      (differenceBit borrow false b::tail.1,tail.2)
  | a::as, b::bs =>
      let tail := subtractBits (borrowBit borrow a b) as bs
      (differenceBit borrow a b::tail.1,tail.2)

theorem subtractBits_length (borrow : Bool) (a b : List Bool) :
    (subtractBits borrow a b).1.length = max a.length b.length := by
  induction a generalizing borrow b with
  | nil =>
      induction b generalizing borrow with
      | nil => simp [subtractBits]
      | cons b bs ih => simp only [subtractBits,List.length_cons,ih,List.length_nil,Nat.zero_max]
  | cons a as ih =>
      cases b with
      | nil => simp only [subtractBits,List.length_cons,ih,List.length_nil,Nat.max_zero]
      | cons b bs =>
          simp only [subtractBits,List.length_cons,ih]
          omega

theorem value_lt_pow_length (bits : List Bool) : Encoding.value bits < 2^bits.length := by
  induction bits with
  | nil => simp [Encoding.value]
  | cons bit bits ih =>
      cases bit <;> simp [Encoding.value,Nat.bit_val,List.length_cons,Nat.pow_succ] <;> omega

theorem subtractBits_value (borrow : Bool) (a b : List Bool) :
    Encoding.value a + 2^(max a.length b.length)*(if (subtractBits borrow a b).2 then 1 else 0) =
      Encoding.value b + (if borrow then 1 else 0) + Encoding.value (subtractBits borrow a b).1 := by
  induction a generalizing borrow b with
  | nil =>
      induction b generalizing borrow with
      | nil => simp [subtractBits,Encoding.value]
      | cons b bs ih =>
          have tail := ih (borrowBit borrow false b)
          simp only [subtractBits,List.length_cons,List.length_nil,Nat.zero_max,Encoding.value,Nat.bit_val,Nat.pow_succ] at tail ⊢
          cases borrow <;> cases b <;> simp [borrowBit,differenceBit] at tail ⊢ <;> split_ifs at tail ⊢ <;> omega
  | cons a as ih =>
      cases b with
      | nil =>
          have tail := ih (borrowBit borrow a false) []
          simp only [subtractBits,List.length_cons,List.length_nil,Nat.max_zero,Encoding.value,Nat.bit_val,Nat.pow_succ] at tail ⊢
          cases borrow <;> cases a <;> simp [borrowBit,differenceBit] at tail ⊢ <;> split_ifs at tail ⊢ <;> omega
      | cons b bs =>
          have tail := ih (borrowBit borrow a b) bs
          have width : max (a::as).length (b::bs).length = max as.length bs.length+1 := by
            simp only [List.length_cons]
            omega
          rw [width,Nat.pow_succ]
          simp only [subtractBits,Encoding.value,Nat.bit_val] at tail ⊢
          cases borrow <;> cases a <;> cases b <;> simp [borrowBit,differenceBit] at tail ⊢ <;> split_ifs at tail ⊢ <;> omega

/-- The final borrow detects precisely unsigned underflow, including a
borrow supplied by a lower-significance block. -/
theorem subtractBits_borrow (borrow : Bool) (a b : List Bool) :
    (subtractBits borrow a b).2 = true ↔
      Encoding.value a < Encoding.value b + (if borrow then 1 else 0) := by
  have equation := subtractBits_value borrow a b
  have smaller := value_lt_pow_length (subtractBits borrow a b).1
  rw [subtractBits_length] at smaller
  constructor
  · intro overflow
    rw [overflow] at equation
    simp only [ite_true,Nat.mul_one] at equation
    omega
  · intro underflow
    cases overflow : (subtractBits borrow a b).2 with
    | true => rfl
    | false =>
        rw [overflow] at equation
        simp only [Bool.false_eq_true,ite_false,Nat.mul_zero,Nat.add_zero] at equation
        omega

/-- Whenever the operands are ordered, the emitted digits represent the
ordinary natural difference. No canonicality assumption is needed. -/
theorem subtractBits_of_le (borrow : Bool) (a b : List Bool)
    (ordered : Encoding.value b + (if borrow then 1 else 0) ≤ Encoding.value a) :
    Encoding.value (subtractBits borrow a b).1 =
      Encoding.value a - (Encoding.value b + (if borrow then 1 else 0)) := by
  have noBorrow : (subtractBits borrow a b).2 = false := by
    have spec := subtractBits_borrow borrow a b
    cases outcome : (subtractBits borrow a b).2 <;> simp_all
    omega
  have equation := subtractBits_value borrow a b
  rw [noBorrow] at equation
  simp only [Bool.false_eq_true,ite_false,Nat.mul_zero,Nat.add_zero] at equation
  omega

/-- Saturating subtraction is specified on every pair of bit strings. -/
def saturatedDifference (a b : List Bool) : List Bool :=
  let result := subtractBits false a b
  if result.2 then [] else result.1

theorem saturatedDifference_value (a b : List Bool) :
    Encoding.value (saturatedDifference a b) = Encoding.value a - Encoding.value b := by
  have spec := subtractBits_borrow false a b
  simp only [Bool.false_eq_true,ite_false,Nat.add_zero] at spec
  unfold saturatedDifference
  by_cases underflow : (subtractBits false a b).2 = true
  · rw [if_pos underflow]
    have less := spec.mp underflow
    simp only [Encoding.value]
    omega
  · rw [if_neg underflow]
    have ordered : Encoding.value b + (if false then 1 else 0) ≤ Encoding.value a := by
      simp only [Bool.false_eq_true,ite_false,Nat.add_zero]
      exact Nat.le_of_not_gt (fun less => underflow (spec.mpr less))
    exact subtractBits_of_le false a b ordered

end Counting.StackMachine.Binary
