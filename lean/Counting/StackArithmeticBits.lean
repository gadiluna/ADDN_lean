import Counting.StackMachine

namespace Counting.StackMachine.Arithmetic

def sumBit (carry a b : Bool) : Bool := xor (xor carry a) b

def carryBit (carry a b : Bool) : Bool := (a && b) || (carry && a) || (carry && b)

theorem fullAdder (carry a b : Bool) :
    (sumBit carry a b).toNat + 2*(carryBit carry a b).toNat = carry.toNat+a.toNat+b.toNat := by
  cases carry <;> cases a <;> cases b <;> decide

def addBits (carry : Bool) : List Bool → List Bool → List Bool
  | [], [] => if carry then [true] else []
  | a::first, [] => sumBit carry a false :: addBits (carryBit carry a false) first []
  | [], b::second => sumBit carry false b :: addBits (carryBit carry false b) [] second
  | a::first, b::second => sumBit carry a b :: addBits (carryBit carry a b) first second

theorem addBits_value (carry : Bool) (first second : List Bool) :
    Encoding.value (addBits carry first second) = Encoding.value first+Encoding.value second+carry.toNat := by
  induction first generalizing second carry with
  | nil =>
      induction second generalizing carry with
      | nil => cases carry <;> simp [addBits, Encoding.value]
      | cons b second ih =>
          rw [addBits]
          simp only [Encoding.value, Nat.bit_val]
          rw [ih]
          have sum := fullAdder carry false b
          simp only [Encoding.value, Bool.toNat_false] at *
          omega
  | cons a first ih =>
      cases second with
      | nil =>
          rw [addBits]
          simp only [Encoding.value, Nat.bit_val]
          rw [ih]
          have sum := fullAdder carry a false
          simp only [Encoding.value, Bool.toNat_false] at *
          omega
      | cons b second =>
          rw [addBits]
          simp only [Encoding.value, Nat.bit_val]
          rw [ih]
          have sum := fullAdder carry a b
          omega

theorem addBits_length (carry : Bool) (first second : List Bool) :
    (addBits carry first second).length ≤ first.length+second.length+1 := by
  induction first generalizing second carry with
  | nil =>
      induction second generalizing carry with
      | nil => cases carry <;> simp [addBits]
      | cons b second ih =>
          have bound := ih (carryBit carry false b)
          simp only [addBits, List.length_cons, List.length_nil] at *
          omega
  | cons a first ih =>
      cases second with
      | nil =>
          have bound := ih (carryBit carry a false) []
          simp only [addBits, List.length_cons, List.length_nil] at *
          omega
      | cons b second =>
          have bound := ih (carryBit carry a b) second
          simp only [addBits, List.length_cons] at *
          omega

/-- Canonical little-endian normalization removes only redundant highest
zero bits, and is later implemented by a stack loop. -/
def normalize : List Bool → List Bool
  | [] => []
  | bit::rest =>
      let tail := normalize rest
      if tail = [] ∧ bit = false then [] else bit::tail

theorem normalize_eq_bits (input : List Bool) : normalize input = (Encoding.value input).bits := by
  induction input with
  | nil => rfl
  | cons bit rest ih =>
      rw [normalize, ih]
      by_cases zero : Encoding.value rest = 0
      · rw [zero, Nat.zero_bits]
        cases bit <;> simp [Encoding.value, Nat.bit_val, zero]
      · have bits : (Encoding.value rest).bits ≠ [] := by
          intro empty
          have equal := congrArg Encoding.value empty
          simp only [Encoding.value_bits, Encoding.value] at equal
          exact zero equal
        rw [if_neg (by simp only [bits, false_and, not_false_eq_true])]
        exact (Nat.bits_append_bit _ _ (fun equal => (zero equal).elim)).symm

theorem normalize_value (input : List Bool) : Encoding.value (normalize input) = Encoding.value input := by
  rw [normalize_eq_bits, Encoding.value_bits]

theorem addBits_natural (first second : Nat) :
    normalize (addBits false first.bits second.bits) = (first+second).bits := by
  rw [normalize_eq_bits, addBits_value, Encoding.value_bits, Encoding.value_bits]
  rfl

end Counting.StackMachine.Arithmetic
