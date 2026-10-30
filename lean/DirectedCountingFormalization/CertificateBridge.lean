import DirectedCountingFormalization.CertificateArithmetic
import DirectedCountingFormalization.Connectivity

/-!
# Graph-to-arithmetic bridges for counting certificates

The arithmetic kernel deliberately indexes the visible strands by naturals
`i < q`.  This file discharges its outgoing-cut assumption from ordinary
strong connectivity of the positive support relation on `Fin q`.
-/

namespace DirectedCounting

/-- Strong connectivity of the positive matrix support supplies every
outgoing cut required by the division-free ratio argument. -/
theorem hasOutgoingCut_of_support_stronglyConnected
    {q : ℕ} {M : ℕ → ℕ → ℕ}
    (hsc : StronglyConnected (fun i j : Fin q ↦ 0 < M i.1 j.1)) :
    HasOutgoingCut q M := by
  intro Q hQ hproper
  obtain ⟨i, hi, hQi⟩ := hQ
  obtain ⟨j, hj, hQj⟩ := hproper
  let S : Set (Fin q) := {k | Q k.1}
  have hSne : ∃ k, k ∈ S := ⟨⟨i, hi⟩, hQi⟩
  have hSproper : ∃ k, k ∉ S := ⟨⟨j, hj⟩, hQj⟩
  obtain ⟨u, v, hu, hv, huv⟩ := exists_edge_leaving hsc hSne hSproper
  exact ⟨u.1, v.1, u.2, v.2, hu, hv, huv⟩

/-- The paper's minimum-ratio loss lemma with support strong connectivity
in place of the arithmetic kernel's equivalent outgoing-cut interface. -/
theorem minimum_ratio_loss_of_support_stronglyConnected
    {q candidate : ℕ}
    {M : ℕ → ℕ → ℕ} {d y old target : ℕ → ℕ}
    {leader : ℕ}
    (hCandidate : candidate = sumN q y)
    (hyPos : ∀ i, i < q → 0 < y i)
    (hleader : leader < q)
    (hyLeader : y leader = 1)
    (hzLeader : target leader = 1)
    (hLarge : candidate < total q target)
    (hMono : ∀ i, i < q → target i ≤ old i)
    (hBalance : BalancedRowSystem q M d y)
    (hsc : StronglyConnected (fun i j : Fin q ↦ 0 < M i.1 j.1))
    (hDemand : ∀ i, i < q → old i = target i →
      rowSum q M target i ≤ d i * target i) :
    ∃ i, IsMinRatio q target y i ∧ target i < old i := by
  exact minimum_ratio_loss hCandidate hyPos hleader hyLeader hzLeader
    hLarge hMono hBalance (hasOutgoingCut_of_support_stronglyConnected hsc)
    hDemand

/-- The normalized matrix subsolution theorem under the support condition
that the local certificate actually checks. -/
theorem normalized_subsolution_eq_of_support_stronglyConnected
    {q : ℕ} {M : ℕ → ℕ → ℕ} {d y b : ℕ → ℕ}
    {leader : ℕ}
    (hyPos : ∀ i, i < q → 0 < y i)
    (hbPos : ∀ i, i < q → 0 < b i)
    (hleader : leader < q)
    (hyLeader : y leader = 1)
    (hbLeader : b leader = 1)
    (hBalance : BalancedRowSystem q M d y)
    (hsc : StronglyConnected (fun i j : Fin q ↦ 0 < M i.1 j.1))
    (hSub : ∀ i, i < q → rowSum q M b i ≤ d i * b i) :
    ∀ i, i < q → b i = y i := by
  exact normalized_subsolution_eq_on hyPos hbPos hleader hyLeader hbLeader
    hBalance (hasOutgoingCut_of_support_stronglyConnected hsc) hSub

end DirectedCounting
