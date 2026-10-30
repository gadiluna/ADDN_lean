import Counting.TimingProtocolLocal

/-!
# Pointed isomorphism of intrinsic history vistas

At each natural level a node is a distinct visible full history. The
separate root is unique and therefore fixed; the distinguished final node
is the observer. Isomorphisms preserve levels, input labels, black parent
edges, red multiplicities and outdegree labels. They need not preserve
agent names, actual population sizes, or hidden anonymity values.
-/

namespace Counting.VistaIsomorphism
open TimingProtocolLocal

theorem occurrences_cast (r a b : Nat) (eq : a = b) (H : FullHistory (r + a)) :
    occurrences r b (cast (congrArg (fun d => FullHistory (r + d)) eq) H) = occurrences r a H := by
  subst b
  rfl

theorem levels_add (r d : Nat) (H : FullHistory (r + d)) :
    levels (r + d) H r = occurrences r d H := by
  unfold levels
  rw [dif_pos (by omega : r ≤ r + d)]
  have h := occurrences_cast r (r + d - r) d (by omega)
    (cast (congrArg FullHistory (Nat.add_sub_of_le (show r ≤ r + d by omega)).symm) H)
  simpa only [cast_cast, cast_eq] using h.symm

@[simp] theorem levels_top (t : Nat) (H : FullHistory t) : levels t H t = {H} :=
  levels_add t 0 H

theorem levels_above (t r : Nat) (H : FullHistory t) (hr : t < r) : levels t H r = ∅ := by
  simp only [levels, dif_neg (by omega : ¬r ≤ t)]

theorem self_mem_levels (t : Nat) (H : FullHistory t) : H ∈ levels t H t := by
  rw [levels_top]
  exact Finset.mem_singleton_self H

theorem levels_succ_of_le (r t : Nat) (H : FullHistory (t + 1)) (hr : r ≤ t) :
    levels (t + 1) H r = levels t H.1 r ∪ H.2.2.toFinset.biUnion (fun h => levels t h r) := by
  classical
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hr
  exact (levels_add r (d + 1) H).trans (congrArg₂ (fun (s u : Finset (FullHistory r)) => s ∪ u)
    (levels_add r d H.1).symm
    (congrArg H.2.2.toFinset.biUnion (funext fun h => (levels_add r d h).symm)))

theorem parent_mem_levels (t : Nat) (H : FullHistory t) (r : Nat)
    (h : FullHistory (r + 1)) (visible : h ∈ levels t H (r + 1)) :
    parent r h ∈ levels t H r := by
  induction t with
  | zero =>
      rw [levels_above 0 (r + 1) H (by omega)] at visible
      exact False.elim (Finset.notMem_empty _ visible)
  | succ t ih =>
      by_cases hrt : r = t
      · subst r
        rw [levels_top, Finset.mem_singleton] at visible
        subst h
        rw [levels_succ_of_le t t H le_rfl]
        exact Finset.mem_union_left _ (self_mem_levels t H.1)
      · have hrt : r + 1 ≤ t := by
          by_contra ht
          rw [levels_above (t + 1) (r + 1) H (by omega)] at visible
          exact Finset.notMem_empty _ visible
        rw [levels_succ_of_le (r + 1) t H hrt] at visible
        rw [levels_succ_of_le r t H (by omega)]
        rcases Finset.mem_union.mp visible with hv | hv
        · exact Finset.mem_union_left _ (ih H.1 hv)
        · obtain ⟨message, hmessage, hv⟩ := Finset.mem_biUnion.mp hv
          exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨message, hmessage, ih message hv⟩)

theorem message_mem_levels (t : Nat) (H : FullHistory t) (r : Nat)
    (h : FullHistory (r + 1)) (visible : h ∈ levels t H (r + 1))
    (old : FullHistory r) (received : old ∈ h.2.2) : old ∈ levels t H r := by
  induction t with
  | zero =>
      rw [levels_above 0 (r + 1) H (by omega)] at visible
      exact False.elim (Finset.notMem_empty _ visible)
  | succ t ih =>
      by_cases hrt : r = t
      · subst r
        rw [levels_top, Finset.mem_singleton] at visible
        subst h
        rw [levels_succ_of_le t t H le_rfl]
        exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr
          ⟨old, Multiset.mem_toFinset.mpr received, self_mem_levels t old⟩)
      · have hrt : r + 1 ≤ t := by
          by_contra ht
          rw [levels_above (t + 1) (r + 1) H (by omega)] at visible
          exact Finset.notMem_empty _ visible
        rw [levels_succ_of_le (r + 1) t H hrt] at visible
        rw [levels_succ_of_le r t H (by omega)]
        rcases Finset.mem_union.mp visible with hv | hv
        · exact Finset.mem_union_left _ (ih H.1 hv)
        · obtain ⟨message, hmessage, hv⟩ := Finset.mem_biUnion.mp hv
          exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨message, hmessage, ih message hv⟩)

abbrev Node {t : Nat} (H : FullHistory t) (r : Nat) := {h : FullHistory r // h ∈ levels t H r}

/-- A pointed, label-preserving isomorphism of the finite layered graph.
The unique root below level zero is fixed implicitly. -/
structure Iso {t : Nat} (H K : FullHistory t) where
  equiv : ∀ r, Node H r ≃ Node K r
  input : ∀ r (a : Node H r), TimingProtocolLocal.input r (equiv r a).val = TimingProtocolLocal.input r a.val
  degree : ∀ r (b : Node H (r + 1)), TimingProtocolLocal.degree r (equiv (r + 1) b).val = TimingProtocolLocal.degree r b.val
  parent : ∀ r (a : Node H r) (b : Node H (r + 1)),
    TimingProtocolLocal.parent r b.val = a.val ↔
      TimingProtocolLocal.parent r (equiv (r + 1) b).val = (equiv r a).val
  red : ∀ r (a : Node H r) (b : Node H (r + 1)),
    TimingProtocolLocal.red r (equiv r a).val (equiv (r + 1) b).val = TimingProtocolLocal.red r a.val b.val
  pointed : (equiv t ⟨H, self_mem_levels t H⟩).val = K

def Iso.refl {t : Nat} (H : FullHistory t) : Iso H H where
  equiv := fun _ => Equiv.refl _
  input := fun _ _ => rfl
  degree := fun _ _ => rfl
  parent := fun _ _ _ => Iff.rfl
  red := fun _ _ _ => rfl
  pointed := rfl

/-- All node histories can be reconstructed from the rooted layered graph:
the input starts the induction, then parent, degree, and red counts recover
each tuple. Red predecessors absent from a level have zero multiplicity. -/
theorem Iso.map_eq {t : Nat} {H K : FullHistory t} (I : Iso H K) :
    ∀ r (a : Node H r), (I.equiv r a).val = a.val := by
  intro r
  induction r with
  | zero =>
      intro a
      exact I.input 0 a
  | succ r ih =>
      intro b
      let old : Node H r := ⟨TimingProtocolLocal.parent r b.val, parent_mem_levels t H r b.val b.property⟩
      have hp := (I.parent r old b).mp rfl
      rw [ih old] at hp
      apply Prod.ext hp
      apply Prod.ext (I.degree r b)
      apply Multiset.ext.mpr
      intro a
      by_cases ha : a ∈ levels t H r
      · let old : Node H r := ⟨a, ha⟩
        have hr := I.red r old b
        rw [ih old] at hr
        exact hr
      · have absentH : a ∉ b.val.2.2 := fun received =>
          ha (message_mem_levels t H r b.val b.property a received)
        have absentK : a ∉ (I.equiv (r + 1) b).val.2.2 := by
          intro received
          have visibleK := message_mem_levels t K r (I.equiv (r + 1) b).val
            (I.equiv (r + 1) b).property a received
          obtain ⟨old, hold⟩ := (I.equiv r).surjective ⟨a, visibleK⟩
          have heq : old.val = a := (ih old).symm.trans (congrArg Subtype.val hold)
          exact ha (heq ▸ old.property)
        rw [Multiset.count_eq_zero_of_notMem absentK, Multiset.count_eq_zero_of_notMem absentH]

/-- Pointed vista isomorphism determines the complete observer history. -/
theorem Iso.history_eq {t : Nat} {H K : FullHistory t} (I : Iso H K) : H = K :=
  (I.map_eq t ⟨H, self_mem_levels t H⟩).symm.trans I.pointed

/-- Full histories are equal exactly when their layered, labeled, pointed
vistas are isomorphic. This holds for arbitrary histories, so in particular
for observers in distinct executions and populations. -/
theorem eq_iff_nonempty_iso {t : Nat} (H K : FullHistory t) : H = K ↔ Nonempty (Iso H K) := by
  constructor
  · intro h
    subst K
    exact ⟨Iso.refl H⟩
  · rintro ⟨I⟩
    exact I.history_eq

theorem actual_history_eq_iff_iso {V W : Type} [Fintype V] [Fintype W]
    (G : Nat → V → V → Nat) (H : Nat → W → W → Nat)
    (labels : V → Bool) (labels' : W → Bool) (t : Nat) (x : V) (y : W) :
    history G labels t x = history H labels' t y ↔
      Nonempty (Iso (history G labels t x) (history H labels' t y)) :=
  eq_iff_nonempty_iso _ _

end Counting.VistaIsomorphism
