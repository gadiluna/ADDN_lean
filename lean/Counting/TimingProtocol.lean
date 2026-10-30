import Counting.TimingProtocolAudit

namespace Counting.TimingProtocol
open DirectedCounting PaperHistory
open TimingProtocolLocal

/-- The mathematical state stores a round and its full local history. -/
abbrev State := (t : ℕ) × FullHistory t

def pack (t : ℕ) (H : FullHistory t) : State := ⟨t, H⟩

def atDepth (t : ℕ) (s : State) : Option (FullHistory t) :=
  if eq : s.1 = t then some (cast (congrArg FullHistory eq) s.2) else none

@[simp] theorem atDepth_pack (t : ℕ) (H : FullHistory t) : atDepth t (pack t H) = some H := by
  simp [atDepth, pack]

/-- All senders supply their previous state; only then is the new outgoing
degree appended. Malformed messages with a wrong depth are ignored. -/
def update (old : State) (messages : Multiset State) (outdegree : ℕ) : State :=
  pack (old.1 + 1) (old.2, outdegree, messages.filterMap (atDepth old.1))

@[simp] theorem update_packed (t : ℕ) (H : FullHistory t)
    (messages : Multiset (FullHistory t)) (outdegree : ℕ) :
    update (pack t H) (messages.map (pack t)) outdegree = pack (t + 1) (H, outdegree, messages) := by
  simp [update, pack, Multiset.filterMap_map, Function.comp_def, atDepth]

noncomputable def coreDecision (ell t : ℕ) (H : FullHistory t) : Option ℕ := by
  classical
  let m := (t + 1) / 2
  exact if ell ≤ m ∧ t = 2 * m - 1 ∧ Pass ell m m t H then some m else none

noncomputable def shortDecision (ell t : ℕ) (H : FullHistory t) : Option ℕ := by
  classical
  let m := t / 2 + 1
  exact if ell < m ∧ t = 2 * m - 2 ∧ Pass ell m (m - 1) t H then some m else none

noncomputable def optimizedDecision (ell t : ℕ) (H : FullHistory t) : Option ℕ := by
  classical
  exact if t = ell then
    if false ∉ levels t H 0 then some ell else none
  else if ell = 1 then coreDecision ell t H else shortDecision ell t H

noncomputable def protocol (decision : (ell t : ℕ) → FullHistory t → Option ℕ) : Protocol State where
  init := fun _ label => pack 0 label
  update := update
  out := fun s ell => decision ell s.1 s.2

noncomputable def core : Protocol State := protocol coreDecision
noncomputable def optimized : Protocol State := protocol optimizedDecision

def optimizedTime (n ell : ℕ) : ℕ :=
  if n = ell then n else if ell = 1 then 2 * n - 1 else 2 * n - 2

variable {V : Type} [Fintype V]
variable (G : ℕ → V → V → ℕ) (leader : V → Bool)

theorem active_messages {A : Type} (edge : V → V → ℕ) (states : V → A) (x : V) :
    (incoming edge (fun y => Status.active (states y)) x).filterMap Status.message = incoming edge states x := by
  rw [← incoming_map edge states x Status.active, Multiset.filterMap_map]
  simp only [Function.comp_def, Status.message, Multiset.filterMap_some]

/-- Until a halt occurs, the mathematical protocol reconstructs exactly
the full-information history, despite using silent-halting trace semantics. -/
theorem trace_step (decision : (ell t : ℕ) → FullHistory t → Option ℕ) (ell t : ℕ)
    (active : ∀ x, (protocol decision).trace ell G leader t x = .active (pack t (history G leader t x)))
    (x : V) :
    (protocol decision).trace ell G leader (t + 1) x =
      match decision ell (t + 1) (history G leader (t + 1) x) with
      | none => .active (pack (t + 1) (history G leader (t + 1) x))
      | some n => .halted (pack (t + 1) (history G leader (t + 1) x)) n := by
  have states : (protocol decision).trace ell G leader t =
      fun x => Status.active (pack t (history G leader t x)) := funext active
  rw [Protocol.trace, states, active_messages]
  rw [← incoming_map (G (t + 1)) (history G leader t) x (pack t)]
  simp only [Protocol.advance, protocol, update_packed, history]
  rfl

/-- A local decision schedule implies simultaneous first halting. This
lemma reasons with the actual silent execution, not an always-active trace. -/
theorem simultaneous_from_decisions
    (decision : (ell t : ℕ) → FullHistory t → Option ℕ) (ell stop output : ℕ)
    (positive : 0 < stop)
    (before : ∀ t, 0 < t → t < stop → ∀ x, decision ell t (history G leader t x) = none)
    (atStop : ∀ x, decision ell stop (history G leader stop x) = some output) :
    (∀ t, t < stop → ∀ x, (protocol decision).trace ell G leader t x = .active (pack t (history G leader t x))) ∧
    (∀ x, (protocol decision).trace ell G leader stop x = .halted (pack stop (history G leader stop x)) output) := by
  have active : ∀ t, t < stop → ∀ x,
      (protocol decision).trace ell G leader t x = .active (pack t (history G leader t x)) := by
    intro t
    induction t with
    | zero => intro _ x; rfl
    | succ t ih =>
      intro ht x
      rw [trace_step G leader decision ell t (ih (by omega)), before (t + 1) (by omega) ht x]
  refine ⟨active, ?_⟩
  obtain ⟨t, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt positive)
  intro x
  rw [trace_step G leader decision ell t (active t (by omega)), atStop x]

end Counting.TimingProtocol
