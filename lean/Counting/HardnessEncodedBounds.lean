import Counting.HardnessEncodedNetwork
import Counting.EncodingTabulateBounds

/-! Polynomial bounds for the entire actual serialized reduction outputs.
The source cardinalities must subsequently be bounded by its explicit
universe encoding; running time is a separate machine simulation theorem. -/
namespace Counting.HardnessEncoded
open Encoding HardnessPath

variable {q m : Nat}

def coefficientWidth (q : Nat) : Nat := (3*q+1)*Nat.size (q+3)+1

theorem graph_bits (inst : X3C.Instance q m) (large : 2 ≤ q) (r : Nat)
    (a b : Agent (X3C.baselineGroups q m)) : (graph inst r a b).size ≤ coefficientWidth q := by
  have coefficient (i : Option (Fin m)) : (inst.coefficient i).size ≤ coefficientWidth q :=
    (inst.coefficient_size large i).trans (Nat.le_succ _)
  have unit : (1 : Nat).size ≤ coefficientWidth q := by simp [coefficientWidth]
  have zero : (0 : Nat).size ≤ coefficientWidth q := Nat.zero_le _
  unfold graph
  split
  · cases a with
    | none => cases b with
      | none => exact zero
      | some b => exact coefficient b.1
    | some a =>
      cases b <;> simp only [pathEdge] <;> split <;> assumption
  · cases a <;> cases b
    · exact zero
    · exact coefficient _
    · exact unit
    · exact zero

def parameterBound (q m : Nat) : Nat := 8*(q+m+3)^2

theorem parameters_bounded (q m : Nat) :
    X3C.baselineMass q m+1 ≤ parameterBound q m ∧
      X3C.base q ≤ parameterBound q m ∧ coefficientWidth q ≤ parameterBound q m := by
  have size : Nat.size (q+3) ≤ q+3 := Nat.size_le.mpr Nat.lt_two_pow_self
  have coeff := Nat.mul_le_mul_left (3*q+1) size
  unfold X3C.baselineMass X3C.base parameterBound coefficientWidth
  constructor
  · nlinarith [Nat.zero_le (q^2), Nat.zero_le (m^2), Nat.zero_le (q*m)]
  constructor <;> nlinarith [Nat.zero_le (q^2), Nat.zero_le (m^2), Nat.zero_le (q*m)]

theorem networkBits_length (inst : X3C.Instance q m) (large : 2 ≤ q) :
    (networkBits inst).length ≤ 12*(parameterBound q m+1)^4 := by
  have bound := tabulate_encoding_length (agents q m).length (X3C.base q)
    (indexedLeader q m) (indexedGraph inst) (coefficientWidth q)
    (fun r _ _ a b => graph_bits inst large r _ _)
  obtain ⟨agentsBound, roundsBound, labelsBound⟩ := parameters_bounded q m
  have population : (agents q m).length ≤ parameterBound q m := by
    rw [agents_length]; exact agentsBound
  exact bound.trans (tabulateLengthBound_polynomial _ _ _ _ population roundsBound labelsBound)

theorem parameterBound_of_input_length (q m L : Nat) (universeBound : q ≤ L) (triples : m ≤ L) :
    parameterBound q m+1 ≤ 73*(L+1)^2 := by
  have size : q+m+3 ≤ 3*(L+1) := by omega
  have square := Nat.pow_le_pow_left size 2
  unfold parameterBound
  nlinarith

def networkSizeConstant : Nat := 12*73^4

theorem networkBits_length_polynomial (inst : X3C.Instance q m) (large : 2 ≤ q)
    (L : Nat) (universeBound : q ≤ L) (triples : m ≤ L) :
    (networkBits inst).length ≤ networkSizeConstant*(L+1)^8 := by
  have power := Nat.pow_le_pow_left (parameterBound_of_input_length q m L universeBound triples) 4
  apply (networkBits_length inst large).trans
  have scaled := Nat.mul_le_mul_left 12 power
  simpa only [mul_pow, ← pow_mul, networkSizeConstant, Nat.mul_assoc] using scaled

def vistaSizeConstant : Nat := 203*(networkSizeConstant+1)^5

theorem vistaBits_length_polynomial (inst : X3C.Instance q m) (large : 2 ≤ q)
    (L : Nat) (universeBound : q ≤ L) (triples : m ≤ L) :
    (vistaBits inst).length ≤ vistaSizeConstant*(L+1)^40 := by
  have network := networkBits_length_polynomial inst large L universeBound triples
  have vista := agentVista_input_length (input inst) (observer inst)
  rw [input_leaderCount] at vista
  have positive : 1 ≤ (L+1)^8 := Nat.one_le_pow 8 _ (by omega)
  have increased : (networkBits inst).length+1 ≤ (networkSizeConstant+1)*(L+1)^8 := by
    nlinarith
  have power := Nat.pow_le_pow_left increased 5
  apply vista.trans
  have scaled := Nat.mul_le_mul_left 203 power
  simpa only [mul_pow, ← pow_mul, vistaSizeConstant, Nat.mul_assoc, networkBits,
    Nat.reduceMul] using scaled

end Counting.HardnessEncoded
