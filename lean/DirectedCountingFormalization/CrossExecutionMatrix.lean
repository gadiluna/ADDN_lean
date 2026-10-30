import DirectedCountingFormalization.CertificateBridge

/-!
# Minimum-ratio loss for arbitrary false target vectors

The quadratic certificate used the minimum-ratio cut only when the visible
target total exceeded the candidate.  For the cross-execution potential the
same cut is needed whenever the target vector differs from the normalized
candidate vector, even when its total is smaller.  The unique leader makes
the minimum-ratio set proper in both cases.
-/

namespace DirectedCounting

/-- Two vectors differ on one of the represented coordinates. -/
def DiffersOn (q : Nat) (x y : Nat → Nat) : Prop :=
  ∃ i, i < q ∧ x i ≠ y i

/-- Division-free minimum-ratio loss for every target vector different from
the leader-normalized candidate.  This is the exact strengthening needed by
the cross-execution potential argument.

`hDemand` is the same explicit history/view accounting bridge as in the
quadratic development: if the matching source class does not lose an agent,
the demand made by matching targets cannot exceed the arcs emitted by that
unchanged class.
-/
theorem minimum_ratio_loss_of_diff
    {q : Nat}
    {M : Nat → Nat → Nat} {d y old target : Nat → Nat}
    {leader : Nat}
    (hyPos : ∀ i, i < q → 0 < y i)
    (hleader : leader < q)
    (hyLeader : y leader = 1)
    (hzLeader : target leader = 1)
    (hDiff : DiffersOn q target y)
    (hMono : ∀ i, i < q → target i ≤ old i)
    (hBalance : BalancedRowSystem q M d y)
    (hCut : HasOutgoingCut q M)
    (hDemand : ∀ i, i < q → old i = target i →
      rowSum q M target i ≤ d i * target i) :
    ∃ i, IsMinRatio q target y i ∧ target i < old i := by
  have hq : 0 < q := by omega
  obtain ⟨base, hbase⟩ := exists_min_ratio (z := target) (y := y) hq hyPos
  let Q : Nat → Prop := fun k => target base * y k = target k * y base
  have hbaseQ : Q base := by simp [Q]
  have hproper : ∃ j, j < q ∧ ¬ Q j := by
    by_contra hex
    have hallQ : ∀ j, j < q → Q j := by
      intro j hj
      by_cases hQj : Q j
      · exact hQj
      · exact False.elim (hex ⟨j, hj, hQj⟩)
    have hbaseLeader := hallQ leader hleader
    have hbaseEq : target base = y base := by
      simpa [Q, hyLeader, hzLeader] using hbaseLeader
    have hyBase : 0 < y base := hyPos base hbase.1
    have htargetEq : ∀ j, j < q → target j = y j := by
      intro j hj
      have he := hallQ j hj
      simp only [Q, hbaseEq] at he
      have he' : y j * y base = target j * y base := by
        simpa [Nat.mul_comm] using he
      exact (Nat.mul_right_cancel hyBase he').symm
    obtain ⟨j, hj, hne⟩ := hDiff
    exact hne (htargetEq j hj)
  obtain ⟨i, j, hi, hj, hiQ, hjQ, hMij⟩ :=
    hCut Q ⟨base, hbase.1, hbaseQ⟩ hproper
  have hyBase : 0 < y base := hyPos base hbase.1
  have hminI : IsMinRatio q target y i :=
    minRatio_transfer hbase hi hiQ hyBase
  have hcrossNe : ¬ target i * y j = target j * y i := by
    intro hij
    apply hjQ
    exact ratioEq_trans hiQ hij (hyPos i hi)
  have hcrossStrict : target i * y j < target j * y i :=
    Nat.lt_of_le_of_ne (hminI.2 j hj) hcrossNe
  have htermMono : ∀ k, k < q →
      target i * (M i k * y k) ≤ y i * (M i k * target k) := by
    intro k hk
    have hs := Nat.mul_le_mul_left (M i k) (hminI.2 k hk)
    simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hs
  have htermStrict :
      target i * (M i j * y j) < y i * (M i j * target j) := by
    have hs := Nat.mul_lt_mul_of_pos_left hcrossStrict hMij
    simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hs
  have hsumStrict := sumN_lt_of_mono_of_lt htermMono j hj htermStrict
  have hweighted :
      target i * rowSum q M y i < y i * rowSum q M target i := by
    simpa [rowSum, mul_sumN, Nat.mul_assoc, Nat.mul_comm,
      Nat.mul_left_comm] using hsumStrict
  have hemitsScaled :
      y i * (d i * target i) < y i * rowSum q M target i := by
    rw [hBalance i hi] at hweighted
    simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hweighted
  have hemits : d i * target i < rowSum q M target i :=
    Nat.lt_of_mul_lt_mul_left hemitsScaled
  have hdrop : target i < old i := by
    have hle := hMono i hi
    by_cases heq : old i = target i
    · have hdemand := hDemand i hi heq
      omega
    · omega
  exact ⟨i, hminI, hdrop⟩

/-- Support-strong-connectivity adapter for `minimum_ratio_loss_of_diff`. -/
theorem minimum_ratio_loss_of_diff_of_support_stronglyConnected
    {q : Nat}
    {M : Nat → Nat → Nat} {d y old target : Nat → Nat}
    {leader : Nat}
    (hyPos : ∀ i, i < q → 0 < y i)
    (hleader : leader < q)
    (hyLeader : y leader = 1)
    (hzLeader : target leader = 1)
    (hDiff : DiffersOn q target y)
    (hMono : ∀ i, i < q → target i ≤ old i)
    (hBalance : BalancedRowSystem q M d y)
    (hsc : StronglyConnected (fun i j : Fin q ↦ 0 < M i.1 j.1))
    (hDemand : ∀ i, i < q → old i = target i →
      rowSum q M target i ≤ d i * target i) :
    ∃ i, IsMinRatio q target y i ∧ target i < old i := by
  exact minimum_ratio_loss_of_diff hyPos hleader hyLeader hzLeader hDiff
    hMono hBalance (hasOutgoingCut_of_support_stronglyConnected hsc) hDemand

/-! ## The fixed-frontier credit spent by a false nonbranching transition -/

/-- Remaining cross-execution credit of one positive reference fiber.

Above the reference size, only the existence of surplus matters.  At and
below the reference size, every additional loss consumes one credit.  For
positive arguments this is the coordinate form of

`surplus + 2 * (reference - classes) - deficit`.
-/
def crossFiberCredit (reference matching : Nat) : Nat :=
  if reference < matching then 2 * reference - 1
  else reference + matching - 2

/-- Positivity of the matching fiber is necessary for strict loss: if its
last representative disappears, truncated natural subtraction makes this
particular credit unable to record the loss.  Equal visible histories are
therefore required to supply the positivity premise used below. -/
theorem crossFiberCredit_zero_loss_counterexample :
    0 < 1 ∧ crossFiberCredit 1 0 = crossFiberCredit 1 1 := by
  decide

/-- Sum of the coordinate credits on one nonbranching frontier. -/
def fixedFrontierCredit (q : Nat) (y z : Nat → Nat) : Nat :=
  sumN q (fun i ↦ crossFiberCredit (y i) (z i))

theorem crossFiberCredit_mono_matching
    {y old target : Nat} (hTarget : target ≤ old) :
    crossFiberCredit y target ≤ crossFiberCredit y old := by
  unfold crossFiberCredit
  split <;> split <;> omega

/-- A loss at or below the reference size strictly spends coordinate credit. -/
theorem crossFiberCredit_strict_of_loss
    {y old target : Nat}
    (hy : 0 < y) (hTargetPos : 0 < target)
    (hBelow : target ≤ y) (hLoss : target < old) :
    crossFiberCredit y target < crossFiberCredit y old := by
  unfold crossFiberCredit
  split <;> split <;> omega

/-- Coordinatewise monotonicity, with one strict loss at or below the
candidate, strictly decreases the full fixed-frontier credit. -/
theorem fixedFrontierCredit_strict_of_loss
    {q : Nat} {y old target : Nat → Nat} {i : Nat}
    (hyPos : ∀ j, j < q → 0 < y j)
    (hTargetPos : ∀ j, j < q → 0 < target j)
    (hMono : ∀ j, j < q → target j ≤ old j)
    (hi : i < q) (hBelow : target i ≤ y i)
    (hLoss : target i < old i) :
    fixedFrontierCredit q y target < fixedFrontierCredit q y old := by
  unfold fixedFrontierCredit
  apply sumN_lt_of_mono_of_lt
  · intro j hj
    exact crossFiberCredit_mono_matching (hMono j hj)
  · exact hi
  · exact crossFiberCredit_strict_of_loss (hyPos i hi)
      (hTargetPos i hi) hBelow hLoss

/-- Every nonbranching target different from the candidate spends the
fixed-frontier credit.  This is the fully composed matrix-to-potential lemma
for the non-equal-target case. -/
theorem fixedFrontierCredit_strict_of_diff
    {q : Nat}
    {M : Nat → Nat → Nat} {d y old target : Nat → Nat}
    {leader : Nat}
    (hyPos : ∀ i, i < q → 0 < y i)
    (hTargetPos : ∀ i, i < q → 0 < target i)
    (hleader : leader < q)
    (hyLeader : y leader = 1)
    (hzLeader : target leader = 1)
    (hDiff : DiffersOn q target y)
    (hMono : ∀ i, i < q → target i ≤ old i)
    (hBalance : BalancedRowSystem q M d y)
    (hCut : HasOutgoingCut q M)
    (hDemand : ∀ i, i < q → old i = target i →
      rowSum q M target i ≤ d i * target i) :
    fixedFrontierCredit q y target < fixedFrontierCredit q y old := by
  obtain ⟨i, hmin, hLoss⟩ := minimum_ratio_loss_of_diff hyPos hleader
    hyLeader hzLeader hDiff hMono hBalance hCut hDemand
  exact fixedFrontierCredit_strict_of_loss hyPos hTargetPos hMono hmin.1
    (minRatio_le_candidate hmin hleader hyLeader hzLeader) hLoss

/-- If the target equals the candidate but some matching source peels, the
same credit strictly decreases.  Clean-transition closure is the separate
semantic argument that supplies such a peel whenever the actual order is
different from the candidate. -/
theorem fixedFrontierCredit_strict_of_equal_target_loss
    {q : Nat} {y old target : Nat → Nat} {i : Nat}
    (hyPos : ∀ j, j < q → 0 < y j)
    (hTargetPos : ∀ j, j < q → 0 < target j)
    (hMono : ∀ j, j < q → target j ≤ old j)
    (hTarget : ∀ j, j < q → target j = y j)
    (hi : i < q) (hLoss : target i < old i) :
    fixedFrontierCredit q y target < fixedFrontierCredit q y old := by
  exact fixedFrontierCredit_strict_of_loss hyPos hTargetPos hMono hi
    (by rw [hTarget i hi]) hLoss

end DirectedCounting
