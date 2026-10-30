import Lean

/-!
Kernel-checked arithmetic for the local counting-certificate argument.

The file intentionally uses only Lean's bundled library.  A strand index is a
natural number `i < q`; this avoids any dependence on Mathlib's finite-sum API.
`sumN q f` is the sum of `f 0, ..., f (q-1)`.
-/

namespace DirectedCounting

def sumN : Nat → (Nat → Nat) → Nat
  | 0, _ => 0
  | q + 1, f => sumN q f + f q

@[simp] theorem sumN_zero (f : Nat → Nat) : sumN 0 f = 0 := rfl

@[simp] theorem sumN_succ (q : Nat) (f : Nat → Nat) :
    sumN (q + 1) f = sumN q f + f q := rfl

theorem sumN_congr {q : Nat} {f g : Nat → Nat}
    (h : ∀ i, i < q → f i = g i) :
    sumN q f = sumN q g := by
  induction q with
  | zero => rfl
  | succ q ih =>
      simp only [sumN_succ]
      rw [ih (fun i hi => h i (by omega))]
      rw [h q (by omega)]

theorem sumN_mono {q : Nat} {f g : Nat → Nat}
    (h : ∀ i, i < q → f i ≤ g i) :
    sumN q f ≤ sumN q g := by
  induction q with
  | zero => simp
  | succ q ih =>
      simp only [sumN_succ]
      have h₁ := ih (fun i hi => h i (by omega))
      have h₂ := h q (by omega)
      omega

theorem sumN_lt_of_mono_of_lt {q : Nat} {f g : Nat → Nat}
    (hmono : ∀ i, i < q → f i ≤ g i)
    (k : Nat) (hk : k < q) (hlt : f k < g k) :
    sumN q f < sumN q g := by
  induction q with
  | zero => omega
  | succ q ih =>
      simp only [sumN_succ]
      by_cases hlast : k = q
      · subst k
        have hp := sumN_mono (q := q)
          (fun i hi => hmono i (by omega))
        have hq := hmono q (by omega)
        omega
      · have hkq : k < q := by omega
        have hp := ih
          (fun i hi => hmono i (by omega)) hkq
        have hq := hmono q (by omega)
        omega

theorem term_le_sumN {q : Nat} (f : Nat → Nat) {i : Nat} (hi : i < q) :
    f i ≤ sumN q f := by
  induction q with
  | zero => omega
  | succ q ih =>
      simp only [sumN_succ]
      by_cases hlast : i = q
      · subst i
        omega
      · have hiq : i < q := by omega
        have hp := ih hiq
        omega

theorem q_le_sumN_of_pos {q : Nat} {f : Nat → Nat}
    (hpos : ∀ i, i < q → 0 < f i) :
    q ≤ sumN q f := by
  induction q with
  | zero => simp
  | succ q ih =>
      simp only [sumN_succ]
      have hp := ih (fun i hi => hpos i (by omega))
      have hq := hpos q (by omega)
      omega

/-! ## Cross-multiplied minimum ratios -/

/-- `i` minimizes `z i / y i`, expressed without division. -/
def IsMinRatio (q : Nat) (z y : Nat → Nat) (i : Nat) : Prop :=
  i < q ∧ ∀ j, j < q → z i * y j ≤ z j * y i

theorem minRatio_le_candidate
    {q : Nat} {z y : Nat → Nat} {i leader : Nat}
    (hmin : IsMinRatio q z y i)
    (hleader : leader < q)
    (hyLeader : y leader = 1)
    (hzLeader : z leader = 1) :
    z i ≤ y i := by
  have h := hmin.2 leader hleader
  simp [hyLeader, hzLeader] at h
  exact h

theorem minRatio_transfer
    {q : Nat} {z y : Nat → Nat} {base i : Nat}
    (hbase : IsMinRatio q z y base)
    (hi : i < q)
    (hiSame : z base * y i = z i * y base)
    (hyBase : 0 < y base) :
    IsMinRatio q z y i := by
  refine ⟨hi, ?_⟩
  intro k hk
  have hs := Nat.mul_le_mul_right (y i) (hbase.2 k hk)
  have hs' : (z i * y k) * y base ≤ (z k * y i) * y base := by
    calc
      (z i * y k) * y base = (z i * y base) * y k := by ac_rfl
      _ = (z base * y i) * y k := by rw [hiSame]
      _ = (z base * y k) * y i := by ac_rfl
      _ ≤ (z k * y base) * y i := hs
      _ = (z k * y i) * y base := by
        ac_rfl
  apply Nat.le_of_mul_le_mul_left (c := y base)
  · simpa [Nat.mul_comm] using hs'
  · exact hyBase

theorem ratioEq_trans
    {z y : Nat → Nat} {base i j : Nat}
    (hiSame : z base * y i = z i * y base)
    (hijSame : z i * y j = z j * y i)
    (hyI : 0 < y i) :
    z base * y j = z j * y base := by
  apply Nat.eq_of_mul_eq_mul_left hyI
  calc
    y i * (z base * y j) = (z base * y i) * y j := by ac_rfl
    _ = (z i * y base) * y j := by rw [hiSame]
    _ = (z i * y j) * y base := by ac_rfl
    _ = (z j * y i) * y base := by rw [hijSame]
    _ = y i * (z j * y base) := by ac_rfl

theorem ratioLe_trans
    {z y : Nat → Nat} {i j k : Nat}
    (hij : z i * y j ≤ z j * y i)
    (hjk : z j * y k ≤ z k * y j)
    (hyJ : 0 < y j) :
    z i * y k ≤ z k * y i := by
  apply Nat.le_of_mul_le_mul_left (c := y j)
  · calc
      y j * (z i * y k) = (z i * y j) * y k := by ac_rfl
      _ ≤ (z j * y i) * y k := Nat.mul_le_mul_right (y k) hij
      _ = (z j * y k) * y i := by ac_rfl
      _ ≤ (z k * y j) * y i := Nat.mul_le_mul_right (y i) hjk
      _ = y j * (z k * y i) := by ac_rfl
  · exact hyJ

theorem exists_min_ratio
    {q : Nat} {z y : Nat → Nat}
    (hq : 0 < q)
    (hyPos : ∀ i, i < q → 0 < y i) :
    ∃ i, IsMinRatio q z y i := by
  induction q with
  | zero => omega
  | succ q ih =>
      by_cases hqZero : q = 0
      · subst q
        refine ⟨0, ⟨by omega, ?_⟩⟩
        intro j hj
        have hj0 : j = 0 := by omega
        subst j
        simp
      · have hqPos : 0 < q := by omega
        have hyPosOld : ∀ i, i < q → 0 < y i :=
          fun i hi => hyPos i (by omega)
        obtain ⟨i, hmin⟩ := ih hqPos hyPosOld
        by_cases hnew : z q * y i ≤ z i * y q
        · refine ⟨q, ⟨by omega, ?_⟩⟩
          intro k hk
          by_cases hkLast : k = q
          · subst k
            simp
          · have hkOld : k < q := by omega
            exact ratioLe_trans hnew (hmin.2 k hkOld)
              (hyPosOld i hmin.1)
        · refine ⟨i, ⟨Nat.lt_succ_of_lt hmin.1, ?_⟩⟩
          intro k hk
          by_cases hkLast : k = q
          · subst k
            exact Nat.le_of_lt (Nat.lt_of_not_ge hnew)
          · exact hmin.2 k (by omega)

/-! ### Cross-multiplied proof of the minimum-ratio loss lemma -/

def rowSum (q : Nat) (M : Nat → Nat → Nat)
    (x : Nat → Nat) (i : Nat) : Nat :=
  sumN q (fun j => M i j * x j)

def total (q : Nat) (z : Nat → Nat) : Nat := sumN q z

def BalancedRowSystem (q : Nat) (M : Nat → Nat → Nat)
    (d y : Nat → Nat) : Prop :=
  ∀ i, i < q → rowSum q M y i = d i * y i

/-- A finite support digraph has an edge leaving every nonempty proper
vertex set.  For a finite digraph this is the exact cut property used from
strong connectivity in the minimum-ratio proof. -/
def HasOutgoingCut (q : Nat) (M : Nat → Nat → Nat) : Prop :=
  ∀ Q : Nat → Prop,
    (∃ i, i < q ∧ Q i) →
    (∃ j, j < q ∧ ¬ Q j) →
    ∃ i j, i < q ∧ j < q ∧ Q i ∧ ¬ Q j ∧ 0 < M i j

theorem mul_sumN (c q : Nat) (f : Nat → Nat) :
    c * sumN q f = sumN q (fun i => c * f i) := by
  induction q with
  | zero => simp
  | succ q ih =>
      simp only [sumN_succ, Nat.mul_add, ih]

/-- Division-free form of the paper's minimum-ratio loss lemma for one
transition.  `hDemand` is the view-closure counting fact: if strand `i`
does not lose an agent, visible demand cannot exceed all arcs emitted by
that unchanged source class. -/
theorem minimum_ratio_loss_cross_multiplied
    {q candidate : Nat}
    {M : Nat → Nat → Nat} {d y old target : Nat → Nat}
    {leader : Nat}
    (hCandidate : candidate = sumN q y)
    (hyPos : ∀ i, i < q → 0 < y i)
    (hleader : leader < q)
    (hyLeader : y leader = 1)
    (hzLeader : target leader = 1)
    (hLarge : candidate < total q target)
    (hMono : ∀ i, i < q → target i ≤ old i)
    (hBalance : BalancedRowSystem q M d y)
    (hCut : HasOutgoingCut q M)
    (hMinExists : ∃ base, IsMinRatio q target y base)
    (hDemand : ∀ i, i < q → old i = target i →
      rowSum q M target i ≤ d i * target i) :
    ∃ i, IsMinRatio q target y i ∧ target i < old i := by
  obtain ⟨base, hbase⟩ := hMinExists
  let Q : Nat → Prop := fun k => target base * y k = target k * y base
  have hbaseQ : Q base := by
    simp [Q]
  have hproper : ∃ j, j < q ∧ ¬ Q j := by
    by_cases hex : ∃ j, j < q ∧ ¬ Q j
    · exact hex
    · exfalso
      have hallQ : ∀ j, j < q → Q j := by
        intro j hj
        by_cases hQj : Q j
        · exact hQj
        · exact False.elim (hex ⟨j, hj, hQj⟩)
      have hbaseLeader := hallQ leader hleader
      have hbaseEq : target base = y base := by
        simpa [Q, hyLeader, hzLeader] using hbaseLeader
      have hyBase : 0 < y base := hyPos base hbase.1
      have hzy : ∀ j, j < q → target j = y j := by
        intro j hj
        have he := hallQ j hj
        simp only [Q, hbaseEq] at he
        have he' : y j * y base = target j * y base := by
          simpa [Nat.mul_comm] using he
        exact (Nat.mul_right_cancel hyBase he').symm
      have hsumEq := sumN_congr hzy
      simp only [total] at hLarge
      rw [hsumEq, ← hCandidate] at hLarge
      omega
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

/-- The same minimum-ratio lemma with existence of a minimum discharged
internally from finiteness and positivity of the candidate coordinates. -/
theorem minimum_ratio_loss
    {q candidate : Nat}
    {M : Nat → Nat → Nat} {d y old target : Nat → Nat}
    {leader : Nat}
    (hCandidate : candidate = sumN q y)
    (hyPos : ∀ i, i < q → 0 < y i)
    (hleader : leader < q)
    (hyLeader : y leader = 1)
    (hzLeader : target leader = 1)
    (hLarge : candidate < total q target)
    (hMono : ∀ i, i < q → target i ≤ old i)
    (hBalance : BalancedRowSystem q M d y)
    (hCut : HasOutgoingCut q M)
    (hDemand : ∀ i, i < q → old i = target i →
      rowSum q M target i ≤ d i * target i) :
    ∃ i, IsMinRatio q target y i ∧ target i < old i := by
  apply minimum_ratio_loss_cross_multiplied hCandidate hyPos hleader
    hyLeader hzLeader hLarge hMono hBalance hCut
  · exact exists_min_ratio (by omega) hyPos
  · exact hDemand

/-! ### Normalized irreducible subsolutions and clean transitions -/

/-- A positive, leader-normalized subsolution of the same irreducible
balanced row system is the candidate vector.  This is the integer,
division-free specialization of both parts of the paper's matrix lemma that
the clean-transition proof actually needs.

The conclusion is equality on the represented indices `i < q`, because the
Core-only encoding uses functions on all naturals rather than `Fin q`.
-/
theorem normalized_subsolution_eq_on
    {q : Nat} {M : Nat → Nat → Nat} {d y b : Nat → Nat}
    {leader : Nat}
    (hyPos : ∀ i, i < q → 0 < y i)
    (hbPos : ∀ i, i < q → 0 < b i)
    (hleader : leader < q)
    (hyLeader : y leader = 1)
    (hbLeader : b leader = 1)
    (hBalance : BalancedRowSystem q M d y)
    (hCut : HasOutgoingCut q M)
    (hSub : ∀ i, i < q → rowSum q M b i ≤ d i * b i) :
    ∀ i, i < q → b i = y i := by
  have hqPos : 0 < q := by
    have hb := hbPos leader hleader
    omega
  obtain ⟨base, hbase⟩ := exists_min_ratio (z := b) (y := y)
    hqPos hyPos
  let Q : Nat → Prop := fun k => b base * y k = b k * y base
  have hbaseQ : Q base := by simp [Q]
  have hproperImpossible : ¬ (∃ j, j < q ∧ ¬ Q j) := by
    intro hproper
    obtain ⟨i, j, hi, hj, hiQ, hjQ, hMij⟩ :=
      hCut Q ⟨base, hbase.1, hbaseQ⟩ hproper
    have hminI : IsMinRatio q b y i :=
      minRatio_transfer hbase hi hiQ (hyPos base hbase.1)
    have hcrossNe : ¬ b i * y j = b j * y i := by
      intro hij
      apply hjQ
      exact ratioEq_trans hiQ hij (hyPos i hi)
    have hcrossStrict : b i * y j < b j * y i :=
      Nat.lt_of_le_of_ne (hminI.2 j hj) hcrossNe
    have htermMono : ∀ k, k < q →
        b i * (M i k * y k) ≤ y i * (M i k * b k) := by
      intro k hk
      have hs := Nat.mul_le_mul_left (M i k) (hminI.2 k hk)
      simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hs
    have htermStrict :
        b i * (M i j * y j) < y i * (M i j * b j) := by
      have hs := Nat.mul_lt_mul_of_pos_left hcrossStrict hMij
      simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hs
    have hsumStrict := sumN_lt_of_mono_of_lt htermMono j hj htermStrict
    have hweighted :
        b i * rowSum q M y i < y i * rowSum q M b i := by
      simpa [rowSum, mul_sumN, Nat.mul_assoc, Nat.mul_comm,
        Nat.mul_left_comm] using hsumStrict
    have hemitsScaled :
        y i * (d i * b i) < y i * rowSum q M b i := by
      rw [hBalance i hi] at hweighted
      simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hweighted
    have hemits : d i * b i < rowSum q M b i :=
      Nat.lt_of_mul_lt_mul_left hemitsScaled
    have hsub := hSub i hi
    omega
  have hallQ : ∀ j, j < q → Q j := by
    intro j hj
    by_cases hQj : Q j
    · exact hQj
    · exact False.elim (hproperImpossible ⟨j, hj, hQj⟩)
  have hbaseLeader := hallQ leader hleader
  have hbaseEq : b base = y base := by
    simpa [Q, hyLeader, hbLeader] using hbaseLeader
  have hyBase : 0 < y base := hyPos base hbase.1
  intro j hj
  have he := hallQ j hj
  simp only [Q, hbaseEq] at he
  have he' : y j * y base = b j * y base := by
    simpa [Nat.mul_comm] using he
  exact (Nat.mul_right_cancel hyBase he').symm

/-- Semantic shell of the clean-transition lemma.

`b` is the common source/target class-size vector supplied by cleanliness.
The two explicitly model-dependent implications are kept as hypotheses:

* saturation of every represented row means that the represented union has
  no outgoing communication arc;
* in a strongly connected communication graph, a nonempty represented union
  with no outgoing arc is the whole network.

Everything between those two semantic facts is checked arithmetic.
-/
theorem clean_transition_counts
    {q candidate actual : Nat}
    {M : Nat → Nat → Nat} {d y b : Nat → Nat} {leader : Nat}
    {NoOutgoing : Prop}
    (hCandidate : candidate = sumN q y)
    (hyPos : ∀ i, i < q → 0 < y i)
    (hbPos : ∀ i, i < q → 0 < b i)
    (hleader : leader < q)
    (hyLeader : y leader = 1)
    (hbLeader : b leader = 1)
    (hBalance : BalancedRowSystem q M d y)
    (hCut : HasOutgoingCut q M)
    (hSub : ∀ i, i < q → rowSum q M b i ≤ d i * b i)
    (hSaturationNoOutgoing :
      (∀ i, i < q → rowSum q M b i = d i * b i) → NoOutgoing)
    (hClosedUnionIsNetwork : NoOutgoing → actual = total q b) :
    actual = candidate := by
  have hbEq : ∀ i, i < q → b i = y i :=
    normalized_subsolution_eq_on hyPos hbPos hleader hyLeader hbLeader
      hBalance hCut hSub
  have hSaturated : ∀ i, i < q → rowSum q M b i = d i * b i := by
    intro i hi
    calc
      rowSum q M b i = rowSum q M y i := by
        apply sumN_congr
        intro j hj
        rw [hbEq j hj]
      _ = d i * y i := hBalance i hi
      _ = d i * b i := by rw [hbEq i hi]
  have hNoOutgoing := hSaturationNoOutgoing hSaturated
  have hActual := hClosedUnionIsNetwork hNoOutgoing
  have hTotalEq : total q b = sumN q y := by
    apply sumN_congr
    exact hbEq
  rw [hActual, hTotalEq, ← hCandidate]

/-! ## A single potential packages both budgets in the paper

For one coordinate, `y i + 1 - z i` is zero while the true size is strictly
above its candidate, becomes one at the crossing to equality, and increases
by one for every later unit of deficit.  Thus it combines the paper's
`q-1` crossing budget and `N-q` deficit budget into one natural-valued
potential bounded between `1` and `N`.
-/

def potential (q : Nat) (y z : Nat → Nat) : Nat :=
  sumN q (fun i => y i + 1 - z i)

theorem potential_mono {q : Nat} {y old new : Nat → Nat}
    (hmono : ∀ i, i < q → new i ≤ old i) :
    potential q y old ≤ potential q y new := by
  apply sumN_mono
  intro i hi
  exact Nat.sub_le_sub_left (hmono i hi) (y i + 1)

theorem potential_strict_of_min_loss
    {q : Nat} {y old new : Nat → Nat} {i : Nat}
    (hmono : ∀ j, j < q → new j ≤ old j)
    (hi : i < q)
    (hbelow : new i ≤ y i)
    (hloss : new i < old i) :
    potential q y old < potential q y new := by
  apply sumN_lt_of_mono_of_lt
      (fun j hj => Nat.sub_le_sub_left (hmono j hj) (y j + 1)) i hi
  exact Nat.sub_lt_sub_left (by omega) hloss

theorem potential_le_candidate
    {q : Nat} {y z : Nat → Nat}
    (hzPos : ∀ i, i < q → 0 < z i) :
    potential q y z ≤ sumN q y := by
  apply sumN_mono
  intro i hi
  have hp := hzPos i hi
  omega

theorem one_le_potential_of_leader
    {q : Nat} {y z : Nat → Nat} {leader : Nat}
    (hleader : leader < q)
    (hyLeader : y leader = 1)
    (hzLeader : z leader = 1) :
    1 ≤ potential q y z := by
  have ht := term_le_sumN (fun i => y i + 1 - z i) hleader
  simp [hyLeader, hzLeader] at ht
  exact ht

/-! ## Large-target loss and bounded frontier -/

def Large (q candidate : Nat) (z : Nat → Nat) : Prop :=
  candidate < total q z

/-- Abstract arithmetic conclusion of the graph-theoretic minimum-ratio
lemma.  The matrix/support proof is deliberately separated from the budget
argument: for every large target, one minimum-ratio coordinate loses an
agent. -/
def LargeTargetLoss (q R candidate : Nat)
    (y : Nat → Nat) (z : Nat → Nat → Nat) : Prop :=
  ∀ h, h < R → Large q candidate (z (h + 1)) →
    ∃ i, IsMinRatio q (z (h + 1)) y i ∧ z (h + 1) i < z h i

/-- The graph/matrix hypotheses of every transition imply the abstract
`LargeTargetLoss` interface consumed by the potential argument. -/
theorem largeTargetLoss_of_matrix_conditions
    {q R candidate : Nat}
    {M : Nat → Nat → Nat → Nat} {d : Nat → Nat → Nat}
    {y : Nat → Nat} {z : Nat → Nat → Nat} {leader : Nat}
    (hCandidate : candidate = sumN q y)
    (hyPos : ∀ i, i < q → 0 < y i)
    (hleader : leader < q)
    (hyLeader : y leader = 1)
    (hzLeader : ∀ h, h ≤ R → z h leader = 1)
    (hMono : ∀ h, h < R → ∀ i, i < q → z (h + 1) i ≤ z h i)
    (hBalance : ∀ h, h < R → BalancedRowSystem q (M h) (d h) y)
    (hCut : ∀ h, h < R → HasOutgoingCut q (M h))
    (hDemand : ∀ h, h < R → ∀ i, i < q → z h i = z (h + 1) i →
      rowSum q (M h) (z (h + 1)) i ≤ d h i * z (h + 1) i) :
    LargeTargetLoss q R candidate y z := by
  intro h hh hlarge
  exact minimum_ratio_loss hCandidate hyPos hleader hyLeader
    (hzLeader (h + 1) (by omega)) hlarge (hMono h hh)
    (hBalance h hh) (hCut h hh) (hDemand h hh)

theorem potential_strict_of_large
    {q R candidate : Nat} {y : Nat → Nat}
    {z : Nat → Nat → Nat} {leader h : Nat}
    (hLoss : LargeTargetLoss q R candidate y z)
    (hh : h < R)
    (hlarge : Large q candidate (z (h + 1)))
    (hleader : leader < q)
    (hyLeader : y leader = 1)
    (hzLeader : z (h + 1) leader = 1)
    (hmono : ∀ i, i < q → z (h + 1) i ≤ z h i) :
    potential q y (z h) < potential q y (z (h + 1)) := by
  obtain ⟨i, hmin, hdrop⟩ := hLoss h hh hlarge
  exact potential_strict_of_min_loss hmono hmin.1
    (minRatio_le_candidate hmin hleader hyLeader hzLeader) hdrop

theorem add_le_after_strict_steps
    (P : Nat → Nat) (a k : Nat)
    (hstep : ∀ t, t < k → P (a + t) < P (a + t + 1)) :
    P a + k ≤ P (a + k) := by
  induction k with
  | zero => simp
  | succ k ih =>
      have hp := ih (fun t ht => hstep t (by omega))
      have hs := hstep k (by omega)
      have hs' : P (a + k) < P (a + (k + 1)) := by
        simpa [Nat.add_assoc] using hs
      omega

/-- After `candidate` transitions, the visible total is at most the
candidate.  This is Corollary 6.3 of the paper, with all finite-window bounds
made explicit. -/
theorem bounded_frontier
    {q R candidate a : Nat} {y : Nat → Nat}
    {z : Nat → Nat → Nat} {leader : Nat}
    (hCandidate : candidate = sumN q y)
    (horizon : a + candidate ≤ R)
    (hleader : leader < q)
    (hyLeader : y leader = 1)
    (hzLeader : ∀ h, h ≤ R → z h leader = 1)
    (hzPos : ∀ h, h ≤ R → ∀ i, i < q → 0 < z h i)
    (hTimeMono : ∀ h k, h ≤ k → k ≤ R → ∀ i, i < q → z k i ≤ z h i)
    (hLoss : LargeTargetLoss q R candidate y z) :
    total q (z (a + candidate)) ≤ candidate := by
  by_cases hgoal : total q (z (a + candidate)) ≤ candidate
  · exact hgoal
  · exfalso
    have hfinalLarge : Large q candidate (z (a + candidate)) := by
      simp only [Large]
      omega
    have hallStrict : ∀ t, t < candidate →
        potential q y (z (a + t)) < potential q y (z (a + t + 1)) := by
      intro t ht
      have htargetLe : a + t + 1 ≤ a + candidate := by omega
      have htargetBound : a + t + 1 ≤ R := by omega
      have hsumMono : total q (z (a + candidate)) ≤
          total q (z (a + t + 1)) := by
        apply sumN_mono
        exact hTimeMono (a + t + 1) (a + candidate)
          htargetLe horizon
      have hlarge : Large q candidate (z (a + t + 1)) := by
        simp only [Large] at hfinalLarge ⊢
        omega
      have hround : a + t < R := by omega
      have hcoordMono : ∀ i, i < q →
          z (a + t + 1) i ≤ z (a + t) i :=
        hTimeMono (a + t) (a + t + 1) (by omega) htargetBound
      exact potential_strict_of_large hLoss hround hlarge hleader hyLeader
        (hzLeader (a + t + 1) htargetBound) hcoordMono
    have hchain := add_le_after_strict_steps
      (fun h => potential q y (z h)) a candidate hallStrict
    have hlower := one_le_potential_of_leader hleader hyLeader
      (hzLeader a (by omega))
    have hupper := potential_le_candidate (y := y)
      (hzPos (a + candidate) horizon)
    rw [← hCandidate] at hupper
    omega

/-! ## Dirty-transition budget -/

/-- A dirty transition loses at least one aligned agent. -/
def DirtyLoses (q R : Nat) (z : Nat → Nat → Nat)
    (clean : Nat → Prop) : Prop :=
  ∀ h, h < R → ¬ clean h → total q (z (h + 1)) < total q (z h)

theorem descent_add_le_after_dirty_steps
    (P : Nat → Nat) (clean : Nat → Prop) (r k : Nat)
    (hdirty : ∀ t, t < k → ¬ clean (r + t))
    (hloss : ∀ t, t < k → P (r + t + 1) < P (r + t)) :
    P (r + k) + k ≤ P r := by
  induction k with
  | zero => simp
  | succ k ih =>
      have hp := ih
        (fun t ht => hdirty t (by omega))
        (fun t ht => hloss t (by omega))
      have hs := hloss k (by omega)
      have hs' : P (r + (k + 1)) < P (r + k) := by
        simpa [Nat.add_assoc] using hs
      omega

/-- From a frontier of total at most `B`, one of the next `B-q+1`
transitions is clean. -/
theorem clean_exists_after_bounded_frontier
    {q R B r : Nat} {z : Nat → Nat → Nat} {clean : Nat → Prop}
    (hwindow : r + (B - q + 1) ≤ R)
    (hstart : total q (z r) ≤ B)
    (hzPos : ∀ h, h ≤ R → ∀ i, i < q → 0 < z h i)
    (hDirtyLoss : DirtyLoses q R z clean) :
    ∃ t, t < B - q + 1 ∧ clean (r + t) := by
  have hqStart : q ≤ total q (z r) :=
    q_le_sumN_of_pos (hzPos r (by omega))
  have hqB : q ≤ B := Nat.le_trans hqStart hstart
  by_cases hex : ∃ t, t < B - q + 1 ∧ clean (r + t)
  · exact hex
  · exfalso
    have hnone := hex
    have hallDirty : ∀ t, t < B - q + 1 → ¬ clean (r + t) := by
      intro t ht hc
      exact hnone ⟨t, ht, hc⟩
    have hallLoss : ∀ t, t < B - q + 1 →
        total q (z (r + t + 1)) < total q (z (r + t)) := by
      intro t ht
      apply hDirtyLoss (r + t)
      · omega
      · exact hallDirty t ht
    have hdescent := descent_add_le_after_dirty_steps
      (fun h => total q (z h)) clean r (B - q + 1) hallDirty hallLoss
    have hqEnd : q ≤ total q (z (r + (B - q + 1))) :=
      q_le_sumN_of_pos (hzPos _ hwindow)
    omega

/-! ## Certificate-length arithmetic -/

/-- The arithmetic core of the local certificate theorem: the length
`2*candidate-q+1` guarantees a bounded frontier followed by a clean
transition. -/
theorem clean_exists_in_certificate
    {q R candidate : Nat} {y : Nat → Nat}
    {z : Nat → Nat → Nat} {leader : Nat} {clean : Nat → Prop}
    (hCandidate : candidate = sumN q y)
    (hLength : 2 * candidate - q + 1 ≤ R)
    (hyPos : ∀ i, i < q → 0 < y i)
    (hleader : leader < q)
    (hyLeader : y leader = 1)
    (hzLeader : ∀ h, h ≤ R → z h leader = 1)
    (hzPos : ∀ h, h ≤ R → ∀ i, i < q → 0 < z h i)
    (hTimeMono : ∀ h k, h ≤ k → k ≤ R → ∀ i, i < q → z k i ≤ z h i)
    (hLargeLoss : LargeTargetLoss q R candidate y z)
    (hDirtyLoss : DirtyLoses q R z clean) :
    ∃ t, t < candidate - q + 1 ∧ clean (candidate + t) := by
  have hqCandidate : q ≤ candidate := by
    rw [hCandidate]
    exact q_le_sumN_of_pos hyPos
  have hHorizon : candidate ≤ R := by omega
  have hbounded : total q (z candidate) ≤ candidate := by
    simpa using (bounded_frontier (a := 0) hCandidate
      (by simpa using hHorizon) hleader hyLeader hzLeader hzPos
      hTimeMono hLargeLoss)
  have hwindow : candidate + (candidate - q + 1) ≤ R := by omega
  exact clean_exists_after_bounded_frontier hwindow hbounded hzPos hDirtyLoss

/-- If every clean transition identifies the actual network order, the
certificate's candidate is the actual order. -/
theorem local_certificate_sound
    {q R candidate actual : Nat} {y : Nat → Nat}
    {z : Nat → Nat → Nat} {leader : Nat} {clean : Nat → Prop}
    (hCandidate : candidate = sumN q y)
    (hLength : 2 * candidate - q + 1 ≤ R)
    (hyPos : ∀ i, i < q → 0 < y i)
    (hleader : leader < q)
    (hyLeader : y leader = 1)
    (hzLeader : ∀ h, h ≤ R → z h leader = 1)
    (hzPos : ∀ h, h ≤ R → ∀ i, i < q → 0 < z h i)
    (hTimeMono : ∀ h k, h ≤ k → k ≤ R → ∀ i, i < q → z k i ≤ z h i)
    (hLargeLoss : LargeTargetLoss q R candidate y z)
    (hDirtyLoss : DirtyLoses q R z clean)
    (hCleanCounts : ∀ h, h < R → clean h → actual = candidate) :
    actual = candidate := by
  obtain ⟨t, ht, hc⟩ := clean_exists_in_certificate hCandidate hLength
    hyPos hleader hyLeader hzLeader hzPos hTimeMono hLargeLoss hDirtyLoss
  apply hCleanCounts (candidate + t)
  · have hqCandidate : q ≤ candidate := by
      rw [hCandidate]
      exact q_le_sumN_of_pos hyPos
    omega
  · exact hc

end DirectedCounting
