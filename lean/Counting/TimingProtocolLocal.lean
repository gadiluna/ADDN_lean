import Counting.ShortAuditCompleteness
import Counting.AllLeaders

/-! Intrinsic history views and certificates. These definitions take only
local histories and the known leader count, never an actual population or
agent identity. Expanded histories are a mathematical specification; the
separate DAG refinement supplies the efficient representation. -/

namespace Counting.TimingProtocolLocal
open DirectedCounting PaperHistory

noncomputable instance historyDecidableEq (r : ℕ) : DecidableEq (FullHistory r) := Classical.decEq _

noncomputable def occurrences (r : ℕ) : (d : ℕ) → FullHistory (r + d) → Finset (FullHistory r)
  | 0, h => by classical exact {h}
  | d + 1, h => by
      classical
      exact occurrences r d h.1 ∪ h.2.2.toFinset.biUnion (occurrences r d)

theorem mem_occurrences (r d : ℕ) (H : FullHistory (r + d)) (h : FullHistory r) :
    h ∈ occurrences r d H ↔ Sees h d H := by
  classical
  induction d with
  | zero => simp [occurrences, Sees]
  | succ d ih => simp [occurrences, Sees, ih]

noncomputable def levels (t : ℕ) (H : FullHistory t) (r : ℕ) : Finset (FullHistory r) := by
  classical
  exact if hr : r ≤ t then occurrences r (t - r)
    (cast (congrArg FullHistory (Nat.add_sub_of_le hr).symm) H) else ∅

def blackAncestor (r : ℕ) : (d : ℕ) → FullHistory (r + d) → FullHistory r
  | 0, H => H
  | d + 1, H => blackAncestor r d H.1

def defaultHistory : (r : ℕ) → FullHistory r
  | 0 => false
  | r + 1 => (defaultHistory r, 0, 0)

def ancestor (r t : ℕ) (H : FullHistory t) : FullHistory r :=
  if hr : r ≤ t then blackAncestor r (t - r)
    (cast (congrArg FullHistory (Nat.add_sub_of_le hr).symm) H) else defaultHistory r

def input (r : ℕ) (H : FullHistory r) : Bool := ancestor 0 r H

def parent (r : ℕ) (H : FullHistory (r + 1)) : FullHistory r := H.1
def degree (r : ℕ) (H : FullHistory (r + 1)) : ℕ := H.2.1
noncomputable def red (r : ℕ) (old : FullHistory r) (new : FullHistory (r + 1)) : ℕ := by
  classical
  exact new.2.2.count old

/-- The semantic certificate shared by core and shorter schedules. It
records precisely the positive normalized anchor and the audited prefix
and suffix conditions needed for soundness. Flat solving is proved in the
completeness theorem and refined separately by the executable solver. -/
structure Certificate (ell m final anchor : ℕ)
    (visible : ∀ r, Finset (FullHistory r))
    (candidate : ∀ r, FullHistory r → ℕ) where
  leader_positive : 0 < ell
  anchor_positive : 1 ≤ anchor
  anchor_le_final : anchor ≤ final
  anchor_candidate_positive : ∀ i ∈ visible anchor, 0 < candidate anchor i
  anchor_leader_candidate :
    (∑ i ∈ (visible anchor).filter (fun c => input anchor c = true), candidate anchor i) = ell
  anchor_total : (∑ i ∈ visible anchor, candidate anchor i) = m
  parent_visible : ∀ r, r < final → ∀ i ∈ visible (r + 1), parent r i ∈ visible r
  children_nonempty : ∀ r, r < final → ∀ u ∈ visible r,
    ((visible (r + 1)).filter (fun i => parent r i = u)).Nonempty
  backward : ∀ r, r < anchor → ∀ u ∈ visible r,
    (∑ i ∈ (visible (r + 1)).filter (fun i => parent r i = u), candidate (r + 1) i) = candidate r u
  candidate_flow : ∀ r, r < anchor → ∀ u ∈ visible r,
    (∑ i ∈ visible (r + 1), if parent r i = u then degree r i * candidate (r + 1) i else 0) =
      ∑ i ∈ visible (r + 1), red r u i * candidate (r + 1) i
  suffix_nonflat : ∀ r, anchor ≤ r → r < final →
    ¬ ∀ u ∈ visible r, ((visible (r + 1)).filter (fun i => parent r i = u)).card = 1
  suffix_audit : ∀ u ∈ visible anchor,
    ((visible final).filter (fun i => ancestor anchor final i = u)).card ≤ candidate anchor u

variable {V : Type} [Fintype V]
variable (G : ℕ → V → V → ℕ) (leader : V → Bool)

noncomputable def nodeHistory (r : ℕ) (c : Node G leader r) : FullHistory r := history G leader r c.out

@[simp] theorem nodeHistory_classOf (r : ℕ) (v : V) :
    nodeHistory G leader r (classOf G leader r v) = history G leader r v := by
  apply (history_eq_iff_sameMultigraphHistory G leader r _ _).mpr
  exact (classOf_eq_iff G leader r _ _).mp (classOf_out G leader r _)

theorem nodeHistory_injective (r : ℕ) : Function.Injective (nodeHistory G leader r) := by
  intro c d heq
  have same := (history_eq_iff_sameMultigraphHistory G leader r c.out d.out).mp heq
  simpa only [classOf_out] using (classOf_eq_iff G leader r c.out d.out).mpr same

theorem cast_history (a b : ℕ) (heq : a = b) (v : V) :
    cast (congrArg FullHistory heq) (history G leader a v) = history G leader b v := by
  cases heq
  rfl

theorem blackAncestor_history (r d : ℕ) (v : V) :
    blackAncestor r d (history G leader (r + d) v) = history G leader r v := by
  induction d with
  | zero => rfl
  | succ d ih => exact ih

@[simp] theorem nodeHistory_input (r : ℕ) (c : Node G leader r) :
    input r (nodeHistory G leader r c) = label G leader r c := by
  unfold input ancestor nodeHistory
  rw [dif_pos (Nat.zero_le r), cast_history G leader r (0 + (r - 0)) (by omega) c.out,
    blackAncestor_history]
  rfl

@[simp] theorem nodeHistory_parent (r : ℕ) (c : Node G leader (r + 1)) :
    parent r (nodeHistory G leader (r + 1) c) = nodeHistory G leader r (PaperHistory.parent G leader r c) := by
  obtain ⟨v, rfl⟩ := Quotient.mk_surjective c
  change parent r (nodeHistory G leader (r + 1) (classOf G leader (r + 1) v)) =
    nodeHistory G leader r (PaperHistory.parent G leader r (classOf G leader (r + 1) v))
  simp only [nodeHistory_classOf, parent_classOf]
  rfl

@[simp] theorem nodeHistory_degree (r : ℕ) (c : Node G leader (r + 1)) :
    degree r (nodeHistory G leader (r + 1) c) = outdegreeLabel G leader r c := rfl

@[simp] theorem nodeHistory_red (r : ℕ) (p : Node G leader r) (c : Node G leader (r + 1)) :
    red r (nodeHistory G leader r p) (nodeHistory G leader (r + 1) c) = redMultiplicity G leader r p c := by
  classical
  change (incoming (G (r + 1)) (history G leader r) c.out).count (nodeHistory G leader r p) = _
  rw [count_incoming]
  unfold redMultiplicity weightedIncomingCount fiber
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro v _
  have heq : history G leader r v = nodeHistory G leader r p ↔ classOf G leader r v = p := by
    rw [← nodeHistory_classOf]
    exact (nodeHistory_injective G leader r).eq_iff
  simp only [heq]

@[simp] theorem nodeHistory_ancestor (r t : ℕ) (hrt : r ≤ t) (c : Node G leader t) :
    ancestor r t (nodeHistory G leader t c) =
      nodeHistory G leader r (CoreHistory.ancestor G leader r t c) := by
  unfold ancestor nodeHistory
  rw [dif_pos hrt, cast_history G leader t (r + (t - r)) (Nat.add_sub_of_le hrt).symm c.out,
    blackAncestor_history]
  exact (nodeHistory_classOf G leader r c.out).symm

/-- The intrinsic visible histories are exactly the image of the actual
visible quotient nodes, with no additional or missing nodes. -/
theorem levels_eq_image (t r : ℕ) (hrt : r ≤ t) (observer : V) :
    levels t (history G leader t observer) r =
      (CoreTiming.levelsAt G leader t observer r).image (nodeHistory G leader r) := by
  classical
  unfold levels
  rw [dif_pos hrt, cast_history G leader t (r + (t - r)) (Nat.add_sub_of_le hrt).symm observer]
  ext H
  rw [mem_occurrences, sees_iff_causal_support]
  simp only [CoreTiming.levelsAt, visibleNodes, Finset.mem_image, causalSupport,
    Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨v, heq, hv⟩
    exact ⟨classOf G leader r v, ⟨v, hv, rfl⟩, (nodeHistory_classOf G leader r v).trans heq.symm⟩
  · rintro ⟨c, ⟨v, hv, hvc⟩, hc⟩
    subst c
    exact ⟨v, hc.symm.trans (nodeHistory_classOf G leader r v), hv⟩

end Counting.TimingProtocolLocal
