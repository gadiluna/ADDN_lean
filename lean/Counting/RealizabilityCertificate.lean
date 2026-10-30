import Counting.TimingProtocolLocal

/-! Compact fixed-order realizability certificates. Counts refer to selected
agents, not full history-fiber anonymities. The verifier's graph contains
only visible nodes and at most one outside vertex per round. -/

namespace Counting.Realizability
open DirectedCounting
open TimingProtocolLocal

abbrev Counts := ∀ r, FullHistory r → ℕ
abbrev Levels := ∀ r, Finset (FullHistory r)

noncomputable def children (visible : Levels) (r : ℕ) (u : FullHistory r) : Finset (FullHistory (r + 1)) :=
  (visible (r + 1)).filter (fun v => parent r v = u)

noncomputable def childCount (visible : Levels) (k : Counts) (r : ℕ) (u : FullHistory r) : ℕ :=
  ∑ v ∈ children visible r u, k (r + 1) v

noncomputable def leaving (visible : Levels) (k : Counts) (r : ℕ) (u : FullHistory r) : ℕ :=
  k r u - childCount visible k r u

noncomputable def supply (visible : Levels) (k : Counts) (r : ℕ) (u : FullHistory r) : ℕ :=
  ∑ v ∈ children visible r u, k (r + 1) v * degree r v

noncomputable def demand (visible : Levels) (k : Counts) (r : ℕ) (u : FullHistory r) : ℕ :=
  ∑ v ∈ visible (r + 1), k (r + 1) v * red r u v

noncomputable def hidden (N : ℕ) (visible : Levels) (k : Counts) (r : ℕ) : ℕ :=
  N - ∑ v ∈ visible (r + 1), k (r + 1) v

noncomputable def initialCount (visible : Levels) (k : Counts) (b : Bool) : ℕ :=
  if (b : FullHistory 0) ∈ visible 0 then k 0 b else 0

abbrev VisibleNode (visible : Levels) (r : ℕ) := {H : FullHistory r // H ∈ visible r}

noncomputable def outsideSize (N : ℕ) (visible : Levels) (k : Counts) (r : ℕ) : ℕ :=
  if 0 < hidden N visible k r then 1 else 0

/-- New nodes, old auxiliary nodes, and a single outside vertex exactly
when the new selected set has fewer than N agents. -/
abbrev RoundVertex (N : ℕ) (visible : Levels) (k : Counts) (r : ℕ) :=
  VisibleNode visible (r + 1) ⊕ (VisibleNode visible r ⊕ Fin (outsideSize N visible k r))

def roundArc (N : ℕ) (visible : Levels) (k : Counts) (r : ℕ) :
    RoundVertex N visible k r → RoundVertex N visible k r → Prop
  | .inl v, .inr (.inl u) => parent r v.val = u.val ∧ 0 < degree r v.val
  | .inr (.inl u), .inl v => 0 < red r u.val v.val
  | .inr (.inr _), .inr (.inl u) => 0 < leaving visible k r u.val
  | .inr (.inl u), .inr (.inr _) =>
      0 < leaving visible k r u.val ∨ demand visible k r u.val < supply visible k r u.val
  | _, _ => False

/-- All tests of the paper's fixed-order certificate, in the intrinsic
history syntax. The parent-closure check explicitly rejects malformed
input syntax; it is derived from every actual vista. -/
structure Certificate (ell N t : ℕ) (H : FullHistory t) (k : Counts) : Prop where
  leaders_positive : 0 < ell
  order_ge_leaders : ell ≤ N
  positive : ∀ r, r ≤ t → ∀ v ∈ levels t H r, 0 < k r v
  bottom_one : k t H = 1
  initial_leaders : initialCount (levels t H) k true ≤ ell
  initial_nonleaders : initialCount (levels t H) k false ≤ N - ell
  parent_visible : ∀ r, r < t → ∀ v ∈ levels t H (r + 1), parent r v ∈ levels t H r
  refinement : ∀ r, r < t → ∀ u ∈ levels t H r,
    childCount (levels t H) k r u ≤ k r u
  balance_full : ∀ r, r < t → hidden N (levels t H) k r = 0 →
    ∀ u ∈ levels t H r, supply (levels t H) k r u = demand (levels t H) k r u
  balance_no_leaving : ∀ r, r < t → 0 < hidden N (levels t H) k r →
    ∀ u ∈ levels t H r, leaving (levels t H) k r u = 0 →
      demand (levels t H) k r u ≤ supply (levels t H) k r u
  connected : ∀ r, r < t → 1 < N → StronglyConnected (roundArc N (levels t H) k r)

end Counting.Realizability
