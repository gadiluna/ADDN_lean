import Counting.HardnessEncodedReduction
import Counting.X3CEncodingCNFBounds
import Counting.ExternalCookLevinSize

/-! End-to-end executable binary maps from actual NP verifiers through
Cook–Levin, CNF, 3SAT, three-dimensional matching and explicit-universe X3C.
This closes the functional and output-size composition. Polynomial machine
time for each generator is still necessary before claiming hardness. -/
namespace Counting.HardnessEncoded.Pipeline
open Encoding Complexity

theorem polynomial_size_composition (n m c k d j : Nat)
    (bounded : m ≤ polynomial c k n) :
    polynomial d j m ≤ polynomial (d*(c+1)^j) (k*j) n := by
  have positive : 1 ≤ (n+1)^k := Nat.one_le_pow k _ (by omega)
  have increased : m+1 ≤ (c+1)*(n+1)^k := by
    unfold polynomial at bounded
    nlinarith
  have power := Nat.mul_le_mul_left d (Nat.pow_le_pow_left increased j)
  simpa only [polynomial, mul_pow, ← pow_mul, Nat.mul_assoc] using power

def x3c (program : Machine.Program) (c k d j : Nat) (word : List Bool) : List Bool :=
  X3CEncoding.CNFReduction.reduce (External.CookLevin.reduce program c k d j word)

def network (program : Machine.Program) (c k d j : Nat) (word : List Bool) : List Bool :=
  networkReduce (x3c program c k d j word)

def vista (program : Machine.Program) (c k d j : Nat) (word : List Bool) : List Bool :=
  vistaReduce (x3c program c k d j word)

def cnfCoefficient (program : Machine.Program) (c k d : Nat) : Nat :=
  External.InitialRows.binaryCoefficient program*(External.CookLevin.widthCoefficient c k d)^4

def cnfExponent (k j : Nat) : Nat := 4*External.CookLevin.widthExponent k j

def x3cCoefficient (program : Machine.Program) (c k d : Nat) : Nat :=
  X3CEncoding.CNFReduction.reductionSizeCoefficient*(cnfCoefficient program c k d+1)^24

def x3cExponent (k j : Nat) : Nat := cnfExponent k j*24

theorem x3c_length (program : Machine.Program) (c k d j : Nat) (word : List Bool) :
    (x3c program c k d j word).length ≤
      polynomial (x3cCoefficient program c k d) (x3cExponent k j) word.length := by
  have initial := External.CookLevin.reduce_length_polynomial program c k d j word
  have next := X3CEncoding.CNFReduction.reduce_length_polynomial
    (External.CookLevin.reduce program c k d j word)
  exact next.trans (polynomial_size_composition _ _ _ _ _ _ initial)

theorem network_length (program : Machine.Program) (c k d j : Nat) (word : List Bool) :
    (network program c k d j word).length ≤
      polynomial (networkReductionSizeConstant*(x3cCoefficient program c k d+1)^8)
        (x3cExponent k j*8) word.length :=
  (networkReduce_length _).trans
    (polynomial_size_composition _ _ _ _ _ _ (x3c_length program c k d j word))

theorem vista_length (program : Machine.Program) (c k d j : Nat) (word : List Bool) :
    (vista program c k d j word).length ≤
      polynomial (vistaReductionSizeConstant*(x3cCoefficient program c k d+1)^40)
        (x3cExponent k j*40) word.length :=
  (vistaReduce_length _).trans
    (polynomial_size_composition _ _ _ _ _ _ (x3c_length program c k d j word))

theorem x3c_correct (program : Machine.Program) (c k d j : Nat)
    (running : RunsIn program (polynomial c k)) (language : Language)
    (verified : ∀ word, word ∈ language ↔ ∃ witness : List Bool,
      witness.length ≤ polynomial d j word.length ∧ Machine.Accepts program (pairWords word witness))
    (word : List Bool) : X3CEncoding.BinaryX3C (x3c program c k d j word) ↔ word ∈ language :=
  (X3CEncoding.CNFReduction.reduce_correct _).trans
    (External.CookLevin.reduce_yes_iff program c k d j running language verified word)

theorem network_correct (program : Machine.Program) (c k d j : Nat)
    (running : RunsIn program (polynomial c k)) (language : Language)
    (verified : ∀ word, word ∈ language ↔ ∃ witness : List Bool,
      witness.length ≤ polynomial d j word.length ∧ Machine.Accepts program (pairWords word witness))
    (word : List Bool) : BinarySomeAgentKnows (network program c k d j word) ↔ word ∉ language :=
  (networkReduce_correct _).trans (not_congr (x3c_correct program c k d j running language verified word))

theorem vista_correct (program : Machine.Program) (c k d j : Nat)
    (running : RunsIn program (polynomial c k)) (language : Language)
    (verified : ∀ word, word ∈ language ↔ ∃ witness : List Bool,
      witness.length ≤ polynomial d j word.length ∧ Machine.Accepts program (pairWords word witness))
    (word : List Bool) : BinaryAtMostOneVista (vista program c k d j word) ↔ word ∉ language :=
  (vistaReduce_correct _).trans (not_congr (x3c_correct program c k d j running language verified word))

/-- Functional maps of polynomial output size for every coNP language.
This is deliberately weaker than `coNPHard`: it supplies no unproved
`ComputesCleanIn` premise for the generating functions. -/
theorem coNP_binary_size_reductions (language : Language) (member : coNP language) :
    ∃ f g : List Bool → List Bool, ∃ cf kf cg kg : Nat,
      (∀ word, (f word).length ≤ polynomial cf kf word.length ∧
        (g word).length ≤ polynomial cg kg word.length) ∧
      (∀ word, BinarySomeAgentKnows (f word) ↔ word ∈ language) ∧
      (∀ word, BinaryAtMostOneVista (g word) ↔ word ∈ language) := by
  obtain ⟨program, c, k, d, j, running, verified⟩ := member
  refine ⟨network program c k d j, vista program c k d j,
    networkReductionSizeConstant*(x3cCoefficient program c k d+1)^8, x3cExponent k j*8,
    vistaReductionSizeConstant*(x3cCoefficient program c k d+1)^40, x3cExponent k j*40,
    fun word => ⟨network_length program c k d j word, vista_length program c k d j word⟩, ?_, ?_⟩
  · intro word
    simpa only [Set.mem_compl_iff, not_not] using
      network_correct program c k d j running languageᶜ verified word
  · intro word
    simpa only [Set.mem_compl_iff, not_not] using
      vista_correct program c k d j running languageᶜ verified word

end Counting.HardnessEncoded.Pipeline
