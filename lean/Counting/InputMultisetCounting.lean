import Counting.InputProtocol
import Counting.ExecutableRefinementCorrectness

/-!
# Running input collection alongside the certified Counting implementation

The Counting component retains its actual compact implementation and its own
silent status. Its messages are filtered separately: after it decides, the
input channel can continue until enough history has been collected. Neither
the population nor agent identities occur in the local interface.

This module is a composition lemma. The concrete local reconstruction function
and its unconditional correctness proof are supplied in the final module.
-/

namespace Counting.InputMultiset

open scoped BigOperators
open Counting.InputProtocol

abbrev View (Input : Type) := (t : Nat) × InputProtocol.FullHistory Input t

def pack {Input : Type} (t : Nat) (h : InputProtocol.FullHistory Input t) : View Input := ⟨t, h⟩

def atDepth {Input : Type} (t : Nat) (s : View Input) :
    Option (InputProtocol.FullHistory Input t) :=
  if eq : s.1 = t then some (cast (congrArg (InputProtocol.FullHistory Input) eq) s.2) else none

def updateView {Input : Type} (old : View Input) (messages : Multiset (View Input))
    (degree : Nat) : View Input :=
  pack (old.1 + 1) (old.2, degree, messages.filterMap (atDepth old.1))

@[simp] theorem updateView_packed {Input : Type} (t : Nat)
    (h : InputProtocol.FullHistory Input t)
    (messages : Multiset (InputProtocol.FullHistory Input t)) (degree : Nat) :
    updateView (pack t h) (messages.map (pack t)) degree =
      pack (t + 1) (h, degree, messages) := by
  simp [updateView, pack, Multiset.filterMap_map, Function.comp_def, atDepth]

structure State (Input : Type) where
  leaders : Nat
  counting : Counting.Status Executable.LocalState
  view : View Input

abbrev Recovery (Input : Type) :=
  (n t : Nat) → InputProtocol.FullHistory Input t → Option (Multiset Input)

noncomputable def update {Input : Type} (old : State Input)
    (messages : Multiset (State Input)) (degree : Nat) : State Input where
  leaders := old.leaders
  counting := Executable.executableProtocol.advance old.leaders old.counting
    ((messages.map State.counting).filterMap Counting.Status.message) degree
  view := updateView old.view (messages.map State.view) degree

def decision {Input : Type} (recover : Recovery Input) (s : State Input) : Option (Multiset Input) :=
  match s.counting with
  | .active _ => none
  | .halted _ n => if 2 * n - 2 ≤ s.view.1 then recover n s.view.1 s.view.2 else none

noncomputable def protocol {Input : Type} (recover : Recovery Input) :
    InputProtocol.Protocol Input (Multiset Input) (State Input) where
  init := fun ell leader input =>
    ⟨ell, .active (Executable.initialState ell leader), pack 0 (leader, input)⟩
  update := update
  out := fun s _ => decision recover s

def terminationTime (n ell : Nat) : Nat :=
  max (TimingProtocol.optimizedTime n ell) (2 * n - 2)

variable {Input V : Type} [Fintype V]
variable (G : Nat → V → V → Nat) (leader : V → Bool) (input : V → Input) (ell : Nat)

noncomputable def physicalState (t : Nat) (x : V) : State Input where
  leaders := ell
  counting := Executable.executableProtocol.trace ell G leader t x
  view := pack t (InputProtocol.history G leader input t x)

theorem update_physicalState (t : Nat) (x : V) :
    update (physicalState G leader input ell t x)
      (Counting.incoming (G (t + 1)) (physicalState G leader input ell t) x)
      (∑ y, G (t + 1) x y) = physicalState G leader input ell (t + 1) x := by
  unfold update physicalState
  simp only [Counting.incoming_map]
  rw [← Counting.incoming_map (G (t + 1)) (InputProtocol.history G leader input t) x (pack t),
    updateView_packed]
  rfl

theorem active_messages {A B : Type} (edge : V → V → Nat) (states : V → A) (x : V) :
    (Counting.incoming edge (fun y => (InputProtocol.Status.active (states y) :
      InputProtocol.Status A B)) x).filterMap InputProtocol.Status.message =
      Counting.incoming edge states x := by
  rw [← Counting.incoming_map edge states x InputProtocol.Status.active, Multiset.filterMap_map]
  simp only [Function.comp_def, InputProtocol.Status.message, Multiset.filterMap_some]

theorem trace_step (recover : Recovery Input) (t : Nat)
    (active : ∀ x, (protocol recover).trace ell G leader input t x =
      .active (physicalState G leader input ell t x)) (x : V) :
    (protocol recover).trace ell G leader input (t + 1) x =
      match decision recover (physicalState G leader input ell (t + 1) x) with
      | none => .active (physicalState G leader input ell (t + 1) x)
      | some result => .halted (physicalState G leader input ell (t + 1) x) result := by
  have all : (protocol recover).trace ell G leader input t =
      fun y => InputProtocol.Status.active (physicalState G leader input ell t y) := funext active
  rw [InputProtocol.Protocol.trace, all, active_messages]
  simp only [InputProtocol.Protocol.advance, protocol, update_physicalState]
  cases decision recover (physicalState G leader input ell (t + 1) x) <;> rfl

theorem decision_before (recover : Recovery Input) (valid : Admissible ell G leader)
    (t : Nat) (before : t < terminationTime (Fintype.card V) ell) (x : V) :
    decision recover (physicalState G leader input ell t x) = none := by
  by_cases hc : t < TimingProtocol.optimizedTime (Fintype.card V) ell
  · obtain ⟨s, _, _, hs⟩ := Executable.executable_before G leader ell valid t hc x
    simp only [decision, physicalState, hs]
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le (Nat.le_of_not_gt hc)
    obtain ⟨s, hs, _⟩ := Executable.executable_halted_silent_forever G leader ell valid d x
    have short : TimingProtocol.optimizedTime (Fintype.card V) ell + d < 2 * Fintype.card V - 2 := by
      unfold terminationTime at before
      omega
    simp only [decision, physicalState, hs, pack, if_neg (Nat.not_le.mpr short)]

theorem decision_at (recover : Recovery Input) (valid : Admissible ell G leader)
    (correct : ∀ t, 2 * Fintype.card V - 2 ≤ t → ∀ x,
      recover (Fintype.card V) t (InputProtocol.history G leader input t x) =
        some (Finset.univ.val.map input)) (x : V) :
    decision recover (physicalState G leader input ell
      (terminationTime (Fintype.card V) ell) x) = some (Finset.univ.val.map input) := by
  have hc : TimingProtocol.optimizedTime (Fintype.card V) ell ≤
      terminationTime (Fintype.card V) ell := Nat.le_max_left _ _
  have ht : 2 * Fintype.card V - 2 ≤ terminationTime (Fintype.card V) ell := Nat.le_max_right _ _
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hc
  obtain ⟨s, hs, _⟩ := Executable.executable_halted_silent_forever G leader ell valid d x
  rw [← hd] at hs
  simp only [decision, physicalState, hs, pack, if_pos ht]
  exact correct _ ht x

theorem simultaneous (recover : Recovery Input) (valid : Admissible ell G leader)
    (correct : ∀ t, 2 * Fintype.card V - 2 ≤ t → ∀ x,
      recover (Fintype.card V) t (InputProtocol.history G leader input t x) =
        some (Finset.univ.val.map input)) :
    (∀ t, t < terminationTime (Fintype.card V) ell → ∀ x,
      (protocol recover).trace ell G leader input t x =
        .active (physicalState G leader input ell t x)) ∧
    (∀ x, (protocol recover).trace ell G leader input (terminationTime (Fintype.card V) ell) x =
      .halted (physicalState G leader input ell (terminationTime (Fintype.card V) ell) x)
        (Finset.univ.val.map input)) := by
  have before : ∀ t, t < terminationTime (Fintype.card V) ell → ∀ x,
      (protocol recover).trace ell G leader input t x =
        .active (physicalState G leader input ell t x) := by
    intro t
    induction t with
    | zero => intro _ x; rfl
    | succ t ih =>
      intro ht x
      rw [trace_step G leader input ell recover t (ih (by omega)),
        decision_before G leader input ell recover valid (t + 1) ht x]
  refine ⟨before, ?_⟩
  have hp : 0 < terminationTime (Fintype.card V) ell :=
    lt_of_lt_of_le (TimingProtocol.optimizedTime_positive G leader ell valid) (Nat.le_max_left _ _)
  obtain ⟨t, ht⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hp)
  intro x
  rw [ht, trace_step G leader input ell recover t (before t (by omega))]
  have atStop := decision_at G leader input ell recover valid correct x
  rw [ht] at atStop
  rw [atStop]

theorem silent_after (recover : Recovery Input) (valid : Admissible ell G leader)
    (correct : ∀ t, 2 * Fintype.card V - 2 ≤ t → ∀ x,
      recover (Fintype.card V) t (InputProtocol.history G leader input t x) =
        some (Finset.univ.val.map input)) (d : Nat) (x : V) :
    (protocol recover).trace ell G leader input (terminationTime (Fintype.card V) ell + d) x =
      .halted (physicalState G leader input ell (terminationTime (Fintype.card V) ell) x)
        (Finset.univ.val.map input) ∧
    ((protocol recover).trace ell G leader input
      (terminationTime (Fintype.card V) ell + d) x).message = none := by
  have forever := (protocol recover).halted_forever ell G leader input _ x _ _
    ((simultaneous G leader input ell recover valid correct).2 x) d
  exact ⟨forever, by rw [forever]; rfl⟩

theorem terminationTime_nonleaders (n ell : Nat) (positive : 0 < ell) (nonleaders : ell < n) :
    terminationTime n ell = TimingProtocol.optimizedTime n ell := by
  unfold terminationTime TimingProtocol.optimizedTime
  split_ifs <;> omega

theorem terminationTime_all_leaders (n : Nat) :
    terminationTime n n = max n (2 * n - 2) := by
  simp [terminationTime, TimingProtocol.optimizedTime]

theorem terminationTime_linear (n ell : Nat) (positive : 0 < ell) (leaders : ell ≤ n) :
    terminationTime n ell ≤ 2 * n - 1 := by
  unfold terminationTime TimingProtocol.optimizedTime
  split_ifs <;> omega

end Counting.InputMultiset
