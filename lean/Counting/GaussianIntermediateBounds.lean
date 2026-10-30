import Counting.GaussianIntermediateElimination

namespace Counting.GaussianBits
open DirectedCounting.VerifiedGaussianAnchorSolver
open RationalSystem
open DirectedCounting.GaussianGeneratorCompleteness
open scoped BigOperators Matrix
variable {q : Nat}

def rationalBits (value : ℚ) : Nat := value.num.natAbs.size + value.den.size
def intermediateBound (q M : Nat) : Nat := 2 * (q * (q.size + (max M 1).size) + 1)
def SystemBound (bound : Nat) (system : RationalSystem q) : Prop :=
  ∀ row column, rationalBits (augmented system row column) ≤ bound

theorem BasisInvariant.system_bound (original : Augmented q ℤ) (permutation : Fin q → Fin q)
    (frontier : Nat) (system : RationalSystem q) (invariant : BasisInvariant original permutation frontier system)
    (M : Nat) (bounded : ∀ i c, (original i c).natAbs ≤ M) : SystemBound (intermediateBound q M) system :=
  fun row column => invariant.entry_bits original permutation frontier system M bounded row column

theorem rationalBits_neg (value : ℚ) : rationalBits (-value) = rationalBits value := by
  simp only [rationalBits, Rat.num_neg_eq_neg_num, Rat.den_neg_eq_den, Int.natAbs_neg]

theorem rationalBits_inv (value : ℚ) (nonzero : value ≠ 0) : rationalBits value⁻¹ = rationalBits value := by
  rw [rationalBits, Rat.den_inv_of_ne_zero nonzero, Rat.num_inv]
  have numerator : value.num ≠ 0 := Rat.num_ne_zero.mpr nonzero
  have sign : value.num.sign.natAbs = 1 := Int.natAbs_sign_of_ne_zero numerator
  simp only [Int.natAbs_mul, sign, Nat.one_mul, Int.natAbs_natCast]
  exact Nat.add_comm _ _

theorem actual_partial_pivot_bound (original : Augmented q ℤ) (permutation : Fin q → Fin q)
    (state : GaussianState q) (pivot : Fin q) (rows : List (Fin q))
    (invariant : BasisInvariant original permutation pivot.val state.system)
    (ok : state.ok = true) (nonzero : state.system.coeff pivot pivot ≠ 0)
    (M : Nat) (bounded : ∀ i c, (original i c).natAbs ≤ M) :
    SystemBound (intermediateBound q M) (eliminateRows pivot rows
      (state.emit (.scale pivot (state.system.coeff pivot pivot)⁻¹))).system := by
  intro row column
  rw [actual_partial_pivot state pivot rows ok nonzero row column]
  split
  · exact (invariant.pivot original permutation state.system pivot nonzero).system_bound
      original permutation (pivot.val+1) (pivotResult state.system pivot) M bounded row column
  · exact invariant.system_bound original permutation pivot.val state.system M bounded row column

def OperationBound (bound : Nat) : RowOp q → Prop
  | .swap _ _ => True
  | .scale _ value | .add _ _ value => rationalBits value ≤ bound

/-- Both execution and independent replay are controlled at every prefix.
The transcript itself stores only rational constants satisfying the same
bound. No assumption about arbitrary caller-supplied transcripts is made. -/
structure SafeState (initial : RationalSystem q) (bound : Nat) (state : GaussianState q) : Prop where
  current : SystemBound bound state.system
  replay_eq : replay initial state.opsRev.reverse = state.system
  prefixes : ∀ length, SystemBound bound (replay initial (state.opsRev.reverse.take length))
  operations : ∀ op ∈ state.opsRev, OperationBound bound op

theorem SafeState.initial (system : RationalSystem q) (bound : Nat) (bounded : SystemBound bound system) :
    SafeState system bound ⟨system, [], true⟩ := by
  exact ⟨bounded, rfl, fun length => by simpa [replay] using bounded, by simp⟩

theorem SafeState.fail (initial : RationalSystem q) (bound : Nat) (state : GaussianState q)
    (safe : SafeState initial bound state) : SafeState initial bound state.fail :=
  ⟨safe.current, safe.replay_eq, safe.prefixes, safe.operations⟩

theorem SafeState.emit (initial : RationalSystem q) (bound : Nat) (state : GaussianState q) (op : RowOp q)
    (safe : SafeState initial bound state) (operation : OperationBound bound op)
    (bounded : SystemBound bound (state.system.applyRowOp op)) :
    SafeState initial bound (state.emit op) := by
  have replayFull : replay initial (state.emit op).opsRev.reverse = (state.emit op).system := by
    simp only [GaussianState.emit, List.reverse_cons, replay_append, safe.replay_eq, replay]
  refine ⟨bounded, replayFull, ?_, ?_⟩
  · intro length
    by_cases before : length ≤ state.opsRev.length
    · simp only [GaussianState.emit, List.reverse_cons]
      rw [List.take_append_of_le_length (by simpa only [List.length_reverse] using before)]
      exact safe.prefixes length
    · have full : (state.emit op).opsRev.reverse.length ≤ length := by
        simp only [GaussianState.emit, List.length_reverse, List.length_cons]
        omega
      rw [List.take_of_length_le full, replayFull]
      exact bounded
  · intro other present
    rcases List.mem_cons.mp present with rfl | present
    · exact operation
    · exact safe.operations other present

theorem eliminateOne_safe (initial : RationalSystem q) (bound : Nat) (state : GaussianState q)
    (pivot target : Fin q) (safe : SafeState initial bound state)
    (bounded : SystemBound bound (eliminateOne pivot state target).system) :
    SafeState initial bound (eliminateOne pivot state target) := by
  by_cases ok : state.ok = true
  · by_cases same : target = pivot
    · simpa only [eliminateOne, ok, if_true, same] using safe
    · simp only [eliminateOne, ok, if_true, same, if_false] at bounded ⊢
      apply safe.emit initial bound state _ _ bounded
      change rationalBits (-state.system.coeff target pivot) ≤ bound
      rw [rationalBits_neg]
      exact safe.current target (some pivot)
  · simpa only [eliminateOne, ok, Bool.false_eq_true, if_false] using safe

theorem eliminateRows_safe (initial : RationalSystem q) (bound : Nat) (state : GaussianState q)
    (pivot : Fin q) (rows : List (Fin q)) (safe : SafeState initial bound state)
    (bounded : ∀ processed : List (Fin q), SystemBound bound (eliminateRows pivot processed state).system) :
    SafeState initial bound (eliminateRows pivot rows state) := by
  induction rows generalizing state with
  | nil => exact safe
  | cons target rest ih =>
      change SafeState initial bound (eliminateRows pivot rest (eliminateOne pivot state target))
      apply ih (eliminateOne pivot state target)
        (eliminateOne_safe initial bound state pivot target safe (bounded [target]))
      intro processed
      exact bounded (target :: processed)

end Counting.GaussianBits
