import Mathlib.Data.Multiset.Filter
import Mathlib.Data.Multiset.MapFold
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

/-!
# Anonymous protocols and full-information histories

This is the semantic model, not the compressed executable vista representation.
Histories contain all messages in the hypothetical always-active execution.
Decoding a history filters messages from agents that the protocol has halted.
Thus full-information indistinguishability remains valid with silent halting.
The protocol has no access to the agent type, graph, or population size.
-/

namespace Counting

open scoped BigOperators

inductive Status (State : Type) where
  | active (state : State)
  | halted (state : State) (output : Nat)
deriving DecidableEq, Repr

def Status.message {State : Type} : Status State → Option State
  | .active s => some s
  | .halted _ _ => none

structure Protocol (State : Type) where
  init : Nat → Bool → State
  update : State → Multiset State → Nat → State
  out : State → Nat → Option Nat

/-- Sending precedes learning this round's outdegree. Halted states are frozen. -/
def Protocol.advance {State : Type} (P : Protocol State) (leaders : Nat)
    (old : Status State) (incoming : Multiset State) (outdegree : Nat) : Status State :=
  match old with
  | .halted s k => .halted s k
  | .active s =>
    let s' := P.update s incoming outdegree
    match P.out s' leaders with
    | none => .active s'
    | some k => .halted s' k

@[simp] theorem Protocol.advance_halted {State : Type} (P : Protocol State)
    (leaders : Nat) (s : State) (k d : Nat) (incoming : Multiset State) :
    P.advance leaders (.halted s k) incoming d = .halted s k := rfl

/-- Expanded histories are used only to state and prove semantic equivalence. -/
def FullHistory : Nat → Type
  | 0 => Bool
  | t + 1 => FullHistory t × Nat × Multiset (FullHistory t)

noncomputable def incoming {V A : Type} [Fintype V]
    (edge : V → V → Nat) (state : V → A) (x : V) : Multiset A :=
  ∑ y, Multiset.replicate (edge y x) (state y)

theorem incoming_map {V A B : Type} [Fintype V]
    (edge : V → V → Nat) (state : V → A) (x : V) (f : A → B) :
    (incoming edge state x).map f = incoming edge (fun y => f (state y)) x := by
  classical
  unfold incoming
  have aux : ∀ (s : Finset V),
      (∑ y ∈ s, Multiset.replicate (edge y x) (state y)).map f =
        ∑ y ∈ s, Multiset.replicate (edge y x) (f (state y)) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | @insert a s ha ih => simp [Finset.sum_insert, ha, Multiset.map_add,
        Multiset.map_replicate, ih]
  simpa using aux Finset.univ

noncomputable def history {V : Type} [Fintype V]
    (G : Nat → V → V → Nat) (leader : V → Bool) :
    (t : Nat) → V → FullHistory t
  | 0, x => leader x
  | t + 1, x =>
      (history G leader t x, ∑ y, G (t + 1) x y,
        incoming (G (t + 1)) (history G leader t) x)

/-- Evaluate any fixed anonymous protocol on a full-information history. -/
def Protocol.decode {State : Type} (P : Protocol State) (leaders : Nat) :
    (t : Nat) → FullHistory t → Status State
  | 0, h => .active (P.init leaders h)
  | t + 1, h => P.advance leaders (P.decode leaders t h.1)
      (h.2.2.filterMap (fun old => (P.decode leaders t old).message)) h.2.1

/-- Execution semantics: only active agents send; halted agents do not update. -/
noncomputable def Protocol.trace {State V : Type} [Fintype V]
    (P : Protocol State) (leaders : Nat) (G : Nat → V → V → Nat)
    (leader : V → Bool) : Nat → V → Status State
  | 0, x => .active (P.init leaders (leader x))
  | t + 1, x => P.advance leaders (P.trace leaders G leader t x)
      ((incoming (G (t + 1)) (P.trace leaders G leader t) x).filterMap Status.message)
      (∑ y, G (t + 1) x y)

/-- Full-information histories determine protocol states, including silent halting. -/
theorem Protocol.trace_eq_decode {State V : Type} [Fintype V]
    (P : Protocol State) (leaders : Nat) (G : Nat → V → V → Nat)
    (leader : V → Bool) (t : Nat) (x : V) :
    P.trace leaders G leader t x = P.decode leaders t (history G leader t x) := by
  induction t generalizing x with
  | zero => rfl
  | succ t ih =>
      simp only [trace, history, decode]
      have hstates : P.trace leaders G leader t =
          fun y => P.decode leaders t (history G leader t y) := by
        funext y
        exact ih y
      rw [hstates, ← incoming_map]
      rw [Multiset.filterMap_map]
      rfl

/-- Cross-network indistinguishability is independent of connectivity or order. -/
theorem Protocol.same_history_same_status {State V W : Type} [Fintype V] [Fintype W]
    (P : Protocol State) (leaders : Nat) (G : Nat → V → V → Nat)
    (H : Nat → W → W → Nat) (leaderV : V → Bool) (leaderW : W → Bool)
    (t : Nat) (x : V) (y : W)
    (h : history G leaderV t x = history H leaderW t y) :
    P.trace leaders G leaderV t x = P.trace leaders H leaderW t y := by
  rw [P.trace_eq_decode, P.trace_eq_decode, h]

/-- A halted process remains silent and retains its decision at all later times. -/
theorem Protocol.halted_forever {State V : Type} [Fintype V]
    (P : Protocol State) (leaders : Nat) (G : Nat → V → V → Nat)
    (leader : V → Bool) (t : Nat) (x : V) (s : State) (k : Nat)
    (h : P.trace leaders G leader t x = .halted s k) (d : Nat) :
    P.trace leaders G leader (t + d) x = .halted s k := by
  induction d with
  | zero => simpa using h
  | succ d ih =>
      rw [Nat.add_succ, trace, ih]
      rfl

/-- The logical lower-bound principle. Safety must be discharged on both networks. -/
theorem Protocol.common_history_prevents_halting
    {State V W : Type} [Fintype V] [Fintype W]
    (P : Protocol State) (leaders : Nat) (G : Nat → V → V → Nat)
    (H : Nat → W → W → Nat) (leaderV : V → Bool) (leaderW : W → Bool)
    (t : Nat) (x : V) (y : W)
    (common : history G leaderV t x = history H leaderW t y)
    (different : Fintype.card V ≠ Fintype.card W)
    (safeV : ∀ s k, P.trace leaders G leaderV t x = .halted s k → k = Fintype.card V)
    (safeW : ∀ s k, P.trace leaders H leaderW t y = .halted s k → k = Fintype.card W) :
    ∃ s, P.trace leaders G leaderV t x = .active s := by
  cases hs : P.trace leaders G leaderV t x with
  | active s => exact ⟨s, rfl⟩
  | halted s k =>
      have hw := (P.same_history_same_status leaders G H leaderV leaderW t x y common).symm.trans hs
      exact False.elim (different ((safeV s k hs).symm.trans (safeW s k hw)))

end Counting
