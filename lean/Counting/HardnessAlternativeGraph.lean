import Counting.HardnessPathSums

namespace Counting.HardnessAlternative
open Counting.HardnessPath DirectedCounting Relation

variable {I : Type} [Fintype I]

/-- A selected suffix's first member relays to its successor. All other
members send directly to the leader. The distinguished group never relays. -/
noncomputable def destination (size : I → Nat) (zero : I) (r : Nat)
    (a : Member size) : Agent size := by
  classical
  exact if h : a.1 ≠ zero ∧ a.2.val = r ∧ a.2.val + 1 < size a.1 then
    some ⟨a.1, ⟨a.2.val + 1, h.2.2⟩⟩ else none

noncomputable def copies (zero : I) (r : Nat) {size : I → Nat} (a : Member size) : Nat := by
  classical
  exact if a.1 = zero ∧ a.2.val = r then 2 else 1

noncomputable def edge (coeff size : I → Nat) (zero : I) (r : Nat) :
    Agent size → Agent size → Nat := by
  classical
  exact fun a b => match a, b with
    | none, none => 0
    | none, some b => coeff b.1
    | some a, b => if destination size zero r a = b then copies zero r a else 0

omit [Fintype I] in
theorem copies_positive (zero : I) (r : Nat) {size : I → Nat} (a : Member size) :
    0 < copies zero r a := by
  unfold copies
  split <;> omega

omit [Fintype I] in
theorem destination_ne_self (size : I → Nat) (zero : I) (r : Nat) (a : Member size) :
    destination size zero r a ≠ some a := by
  unfold destination
  split
  · intro equal
    have position := congrArg (fun b : Member size => b.2.val) (Option.some.inj equal)
    dsimp at position
    omega
  · intro equal
    cases equal

omit [Fintype I] in
theorem destination_after_relay (size : I → Nat) (zero : I) (r : Nat) (a b : Member size)
    (relay : destination size zero r a = some b) : destination size zero r b = none := by
  unfold destination at relay ⊢
  split at relay
  · rename_i condition
    have position := congrArg (fun c : Member size => c.2.val) (Option.some.inj relay)
    dsimp at position
    have different : b.2.val ≠ r := by omega
    simp only [different, false_and, and_false, dite_false]
  · cases relay

omit [Fintype I] in
theorem loopless (coeff size : I → Nat) (zero : I) (r : Nat) (a : Agent size) :
    edge coeff size zero r a a = 0 := by
  cases a with
  | none => rfl
  | some a => exact if_neg (destination_ne_self size zero r a)

omit [Fintype I] in
theorem to_leader (coeff size : I → Nat) (zero : I) (r : Nat) (a : Member size) :
    ReflTransGen (fun x y => 0 < edge coeff size zero r x y) (some a) none := by
  cases target : destination size zero r a with
  | none => exact .single (by simpa only [edge, target, if_true] using copies_positive zero r a)
  | some b =>
      have final := destination_after_relay size zero r a b target
      have first : 0 < edge coeff size zero r (some a) (some b) := by
        simpa only [edge, target, if_true] using copies_positive zero r a
      have last : 0 < edge coeff size zero r (some b) none := by
        simpa only [edge, final, if_true] using copies_positive zero r b
      exact ReflTransGen.trans (.single first) (.single last)

omit [Fintype I] in
theorem connected (coeff size : I → Nat) (zero : I) (r : Nat) (positive : ∀ i, 0 < coeff i) :
    StronglyConnected (fun a b => 0 < edge coeff size zero r a b) := by
  intro a b
  have first : ReflTransGen (fun x y => 0 < edge coeff size zero r x y) a none := by
    cases a with
    | none => exact .refl
    | some a => exact to_leader coeff size zero r a
  have last : ReflTransGen (fun x y => 0 < edge coeff size zero r x y) none b := by
    cases b with
    | none => exact .refl
    | some b => exact .single (positive b.1)
  exact first.trans last

theorem member_outdegree (coeff size : I → Nat) (zero : I) (r : Nat) (a : Member size) :
    (∑ b : Agent size, edge coeff size zero r (some a) b) = copies zero r a := by
  classical
  simp [edge]

theorem leader_outdegree (coeff size : I → Nat) (zero : I) (r : Nat) :
    (∑ b : Agent size, edge coeff size zero r none b) = ∑ i, coeff i * size i := by
  simpa only [edge, HardnessPath.edge, Fintype.sum_option] using
    HardnessPath.leader_outdegree coeff size

end Counting.HardnessAlternative
