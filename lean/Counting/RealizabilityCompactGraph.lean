import Counting.RealizabilityVerifier
import Counting.RealizabilityActiveReachability

namespace Counting.RealizabilityVerifier.CompactGraph
open Counting.Executable

/-- The final slot represents the hidden population, regardless of its size. -/
abbrev Slot (vista : Vista) := Fin (vista.nodes.size + 1)

def isNew (vista : Vista) (r : Nat) (i : Slot vista) : Bool :=
  decide (i.val < vista.nodes.size ∧ (vista.node i.val).level = r + 1)

def isOld (vista : Vista) (r : Nat) (i : Slot vista) : Bool :=
  decide (i.val < vista.nodes.size ∧ (vista.node i.val).level = r)

def isOutside (N : Nat) (vista : Vista) (weights : Array Nat) (r : Nat)
    (i : Slot vista) : Bool :=
  decide (i.val = vista.nodes.size ∧ 0 < hidden N vista weights r)

def active (N : Nat) (vista : Vista) (weights : Array Nat) (r : Nat)
    (i : Slot vista) : Bool :=
  isNew vista r i || isOld vista r i || isOutside N vista weights r i

abbrev Vertex (N : Nat) (vista : Vista) (weights : Array Nat) (r : Nat) :=
  {i : Slot vista // active N vista weights r i = true}

/-- Four bounded-index tests give exactly the certificate's auxiliary arcs. -/
def arc (N : Nat) (vista : Vista) (weights : Array Nat) (r : Nat)
    (x y : Slot vista) : Bool :=
  (isNew vista r x && isOld vista r y &&
    ((vista.node x.val).parent == some y.val && 0 < (vista.node x.val).degree)) ||
  (isOld vista r x && isNew vista r y && 0 < countFrom (vista.node y.val) x.val) ||
  (isOutside N vista weights r x && isOld vista r y && 0 < leaving vista weights r y.val) ||
  (isOld vista r x && isOutside N vista weights r y &&
    (0 < leaving vista weights r x.val || demand vista weights r x.val < supply vista weights r x.val))

def embedSlot (N : Nat) (vista : Vista) (weights : Array Nat) (r : Nat) :
    RoundVertex N vista weights r → Slot vista
  | .inl v => ⟨v.val.val, by have := v.val.isLt; omega⟩
  | .inr (.inl u) => ⟨u.val.val, by have := u.val.isLt; omega⟩
  | .inr (.inr _) => ⟨vista.nodes.size, by omega⟩

theorem outside_positive (N : Nat) (vista : Vista) (weights : Array Nat) (r : Nat)
    (i : Fin (outsideSize N vista weights r)) : 0 < hidden N vista weights r := by
  have bound := i.isLt
  unfold outsideSize at bound
  split_ifs at bound with positive
  · exact positive
  · omega

@[simp] theorem embed_new_roles (N : Nat) (vista : Vista) (weights : Array Nat) (r : Nat)
    (v : LevelIndex vista (r + 1)) :
    isNew vista r (embedSlot N vista weights r (.inl v)) = true ∧
    isOld vista r (embedSlot N vista weights r (.inl v)) = false ∧
    isOutside N vista weights r (embedSlot N vista weights r (.inl v)) = false := by
  have inside := v.val.isLt
  have level := v.property
  simp [isNew,isOld,isOutside,embedSlot,inside,level,show v.val.val ≠ vista.nodes.size by omega]

@[simp] theorem embed_old_roles (N : Nat) (vista : Vista) (weights : Array Nat) (r : Nat)
    (u : LevelIndex vista r) :
    isNew vista r (embedSlot N vista weights r (.inr (.inl u))) = false ∧
    isOld vista r (embedSlot N vista weights r (.inr (.inl u))) = true ∧
    isOutside N vista weights r (embedSlot N vista weights r (.inr (.inl u))) = false := by
  have inside := u.val.isLt
  have level := u.property
  simp [isNew,isOld,isOutside,embedSlot,inside,level,show u.val.val ≠ vista.nodes.size by omega]

@[simp] theorem embed_outside_roles (N : Nat) (vista : Vista) (weights : Array Nat) (r : Nat)
    (i : Fin (outsideSize N vista weights r)) :
    isNew vista r (embedSlot N vista weights r (.inr (.inr i))) = false ∧
    isOld vista r (embedSlot N vista weights r (.inr (.inr i))) = false ∧
    isOutside N vista weights r (embedSlot N vista weights r (.inr (.inr i))) = true := by
  simp [isNew,isOld,isOutside,embedSlot,outside_positive N vista weights r i]

theorem embed_active (N : Nat) (vista : Vista) (weights : Array Nat) (r : Nat)
    (v : RoundVertex N vista weights r) : active N vista weights r (embedSlot N vista weights r v) = true := by
  rcases v with v | u | i
  · obtain ⟨hn,ho,hx⟩ := embed_new_roles N vista weights r v
    simp only [active,hn,ho,hx,Bool.true_or]
  · obtain ⟨hn,ho,hx⟩ := embed_old_roles N vista weights r u
    simp only [active,hn,ho,hx,Bool.false_or,Bool.true_or]
  · obtain ⟨hn,ho,hx⟩ := embed_outside_roles N vista weights r i
    simp only [active,hn,ho,hx,Bool.false_or]

def embed (N : Nat) (vista : Vista) (weights : Array Nat) (r : Nat)
    (v : RoundVertex N vista weights r) : Vertex N vista weights r :=
  ⟨embedSlot N vista weights r v,embed_active N vista weights r v⟩

theorem embed_injective (N : Nat) (vista : Vista) (weights : Array Nat) (r : Nat) :
    Function.Injective (embed N vista weights r) := by
  intro x y same
  have values := congrArg (fun v : Vertex N vista weights r => v.val.val) same
  rcases x with v | u | i <;> rcases y with w | z | j
  all_goals change _ = _ at values
  · congr 1; apply Subtype.ext; exact Fin.ext values
  · have hv := v.property; have hz := z.property
    change v.val.val = z.val.val at values
    rw [values] at hv
    omega
  · have bound := v.val.isLt; change v.val.val = vista.nodes.size at values; omega
  · have hu := u.property; have hw := w.property
    change u.val.val = w.val.val at values
    rw [values] at hu
    omega
  · congr 2; apply Subtype.ext; exact Fin.ext values
  · have bound := u.val.isLt; change u.val.val = vista.nodes.size at values; omega
  · have bound := w.val.isLt; change vista.nodes.size = w.val.val at values; omega
  · have bound := z.val.isLt; change vista.nodes.size = z.val.val at values; omega
  · have hi := i.isLt; have hj := j.isLt
    unfold outsideSize at hi hj
    split_ifs at hi hj <;> congr 2 <;> apply Fin.ext <;> omega

theorem embed_surjective (N : Nat) (vista : Vista) (weights : Array Nat) (r : Nat) :
    Function.Surjective (embed N vista weights r) := by
  intro x
  have isActive := x.property
  simp only [active,Bool.or_eq_true,isNew,isOld,isOutside,decide_eq_true_eq] at isActive
  rcases isActive with (⟨inside,level⟩ | ⟨inside,level⟩) | ⟨last,positive⟩
  · refine ⟨.inl ⟨⟨x.val.val,inside⟩,level⟩,?_⟩
    apply Subtype.ext; apply Fin.ext; rfl
  · refine ⟨.inr (.inl ⟨⟨x.val.val,inside⟩,level⟩),?_⟩
    apply Subtype.ext; apply Fin.ext; rfl
  · refine ⟨.inr (.inr ⟨0,by simp [outsideSize,positive]⟩),?_⟩
    apply Subtype.ext; apply Fin.ext; exact last.symm

/-- Both levels occupy disjoint slots; no validity assumption on the vista is needed. -/
noncomputable def vertexEquiv (N : Nat) (vista : Vista) (weights : Array Nat) (r : Nat) :
    RoundVertex N vista weights r ≃ Vertex N vista weights r :=
  Equiv.ofBijective (embed N vista weights r)
    ⟨embed_injective N vista weights r,embed_surjective N vista weights r⟩

@[simp] theorem isNew_embed (N : Nat) (vista : Vista) (weights : Array Nat) (r : Nat)
    (v : RoundVertex N vista weights r) :
    isNew vista r (embedSlot N vista weights r v) =
      match v with | .inl _ => true | _ => false := by
  rcases v with v | u | i
  · exact (embed_new_roles N vista weights r v).1
  · exact (embed_old_roles N vista weights r u).1
  · exact (embed_outside_roles N vista weights r i).1

@[simp] theorem isOld_embed (N : Nat) (vista : Vista) (weights : Array Nat) (r : Nat)
    (v : RoundVertex N vista weights r) :
    isOld vista r (embedSlot N vista weights r v) =
      match v with | .inr (.inl _) => true | _ => false := by
  rcases v with v | u | i
  · exact (embed_new_roles N vista weights r v).2.1
  · exact (embed_old_roles N vista weights r u).2.1
  · exact (embed_outside_roles N vista weights r i).2.1

@[simp] theorem isOutside_embed (N : Nat) (vista : Vista) (weights : Array Nat) (r : Nat)
    (v : RoundVertex N vista weights r) :
    isOutside N vista weights r (embedSlot N vista weights r v) =
      match v with | .inr (.inr _) => true | _ => false := by
  rcases v with v | u | i
  · exact (embed_new_roles N vista weights r v).2.2
  · exact (embed_old_roles N vista weights r u).2.2
  · exact (embed_outside_roles N vista weights r i).2.2

theorem arc_embed (N : Nat) (vista : Vista) (weights : Array Nat) (r : Nat)
    (x y : RoundVertex N vista weights r) :
    arc N vista weights r (embedSlot N vista weights r x) (embedSlot N vista weights r y) =
      roundArc N vista weights r x y := by
  rcases x with v | u | i <;> rcases y with w | z | j <;>
    simp only [arc,isNew_embed,isOld_embed,isOutside_embed,
      Bool.false_and,Bool.true_and,Bool.or_false,Bool.false_or,Bool.and_false,Bool.and_true] <;> rfl

theorem connected_equivalent (N : Nat) (vista : Vista) (weights : Array Nat) (r : Nat) :
    DirectedCounting.StronglyConnected (fun x y => roundArc N vista weights r x y = true) ↔
    DirectedCounting.StronglyConnected (fun x y : Vertex N vista weights r =>
      arc N vista weights r x.val y.val = true) := by
  apply connected_equiv (vertexEquiv N vista weights r)
  intro x y
  change roundArc N vista weights r x y = true ↔
    arc N vista weights r (embedSlot N vista weights r x) (embedSlot N vista weights r y) = true
  rw [arc_embed]

theorem arc_active (N : Nat) (vista : Vista) (weights : Array Nat) (r : Nat)
    (x y : Slot vista) (edge : arc N vista weights r x y = true) :
    active N vista weights r x = true ∧ active N vista weights r y = true := by
  simp only [arc,Bool.or_eq_true,Bool.and_eq_true] at edge
  simp only [active,Bool.or_eq_true]
  rcases edge with ((⟨⟨xn,yo⟩,_⟩ | ⟨⟨xo,yn⟩,_⟩) | ⟨⟨xx,yo⟩,_⟩) | ⟨⟨xo,yx⟩,_⟩
  · exact ⟨Or.inl (Or.inl xn),Or.inl (Or.inr yo)⟩
  · exact ⟨Or.inl (Or.inr xo),Or.inl (Or.inl yn)⟩
  · exact ⟨Or.inr xx,Or.inl (Or.inr yo)⟩
  · exact ⟨Or.inl (Or.inr xo),Or.inr yx⟩

theorem vertex_card_bound (N : Nat) (vista : Vista) (weights : Array Nat) (r : Nat) :
    Fintype.card (Vertex N vista weights r) ≤ vista.nodes.size + 1 := by
  exact (Fintype.card_subtype_le _).trans (by simp [Slot])

theorem roundVertex_card_sharp (N : Nat) (vista : Vista) (weights : Array Nat) (r : Nat) :
    Fintype.card (RoundVertex N vista weights r) ≤ vista.nodes.size + 1 := by
  rw [Fintype.card_congr (vertexEquiv N vista weights r)]
  exact vertex_card_bound N vista weights r

/-- The explicit carrier has exactly `nodes.size + 1` slots. Inactive
slots are skipped at both ends of the bounded reachability test. -/
def check (N : Nat) (vista : Vista) (weights : Array Nat) (r : Nat) : Bool :=
  activeConnectedCheck (active N vista weights r) (arc N vista weights r)

theorem check_iff (N : Nat) (vista : Vista) (weights : Array Nat) (r : Nat) :
    check N vista weights r = true ↔ connectedCheck (roundArc N vista weights r) = true := by
  rw [check,activeConnectedCheck_iff _ _ (fun x y edge => (arc_active N vista weights r x y edge).2),
    connectedCheck_iff]
  exact (connected_equivalent N vista weights r).symm

theorem check_eq (N : Nat) (vista : Vista) (weights : Array Nat) (r : Nat) :
    check N vista weights r = connectedCheck (roundArc N vista weights r) := by
  have same := check_iff N vista weights r
  cases h : check N vista weights r <;> cases g : connectedCheck (roundArc N vista weights r) <;>
    simp_all

end Counting.RealizabilityVerifier.CompactGraph
