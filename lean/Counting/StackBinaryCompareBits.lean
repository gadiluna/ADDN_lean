import Counting.MachineArithmeticCompare

namespace Counting.StackMachine.Binary

def compareBits (previous : Bool) : List Bool → List Bool → Bool
  | [], [] => previous
  | a::as, [] => compareBits (Machine.compareColumn previous a false) as []
  | [], b::bs => compareBits (Machine.compareColumn previous false b) [] bs
  | a::as, b::bs => compareBits (Machine.compareColumn previous a b) as bs

theorem compareBits_correct (previous : Bool) (first second : List Bool) :
    compareBits previous first second = true ↔
      Encoding.value first < Encoding.value second ∨
      (Encoding.value first = Encoding.value second ∧ previous = true) := by
  induction first generalizing previous second with
  | nil =>
      induction second generalizing previous with
      | nil => simp [compareBits,Encoding.value]
      | cons b bs ih =>
          rw [compareBits,ih]
          cases b <;> cases previous <;> simp [Machine.compareColumn,Encoding.value,Nat.bit_val] <;> omega
  | cons a as ih =>
      cases second with
      | nil =>
          rw [compareBits,ih]
          cases a <;> cases previous <;> simp [Machine.compareColumn,Encoding.value,Nat.bit_val]
      | cons b bs =>
          rw [compareBits,ih]
          cases a <;> cases b <;> cases previous <;>
            simp [Machine.compareColumn,Encoding.value,Nat.bit_val] <;> omega

theorem compareBits_le (first second : List Bool) :
    compareBits true first second = true ↔ Encoding.value first ≤ Encoding.value second := by
  rw [compareBits_correct]
  simp only [and_true]
  omega

theorem compareBits_lt (first second : List Bool) :
    compareBits false first second = true ↔ Encoding.value first < Encoding.value second := by
  rw [compareBits_correct]
  simp

end Counting.StackMachine.Binary
