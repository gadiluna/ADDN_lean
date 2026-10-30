import Counting.Protocol

/-!
# Anonymous protocols with private inputs and arbitrary outputs

This extends the Counting execution model with an initial input at every agent.
The protocol sees only the common leader count, its own leader flag and input,
its previous local state, incoming messages, and its current outdegree. In
particular neither identities nor the population size are protocol arguments.
As in `Counting.Protocol`, a halted process sends no messages and never updates.
-/

namespace Counting.InputProtocol

open scoped BigOperators

inductive Status (State Output : Type) where
  | active (state : State)
  | halted (state : State) (output : Output)
deriving DecidableEq, Repr

def Status.message {State Output : Type} : Status State Output → Option State
  | .active s => some s
  | .halted _ _ => none

structure Protocol (Input Output State : Type) where
  init : Nat → Bool → Input → State
  update : State → Multiset State → Nat → State
  out : State → Nat → Option Output

/-- Messages are sent before the sender learns this round's outdegree. -/
def Protocol.advance {Input Output State : Type} (P : Protocol Input Output State)
    (leaders : Nat) (old : Status State Output) (incoming : Multiset State)
    (outdegree : Nat) : Status State Output :=
  match old with
  | .halted s k => .halted s k
  | .active s =>
    let s' := P.update s incoming outdegree
    match P.out s' leaders with
    | none => .active s'
    | some k => .halted s' k

@[simp] theorem Protocol.advance_halted {Input Output State : Type}
    (P : Protocol Input Output State) (leaders : Nat) (s : State)
    (k : Output) (d : Nat) (incoming : Multiset State) :
    P.advance leaders (.halted s k) incoming d = .halted s k := rfl

/-- Mathematical full-information histories retain the initial input. -/
def FullHistory (Input : Type) : Nat → Type
  | 0 => Bool × Input
  | t + 1 => FullHistory Input t × Nat × Multiset (FullHistory Input t)

/-- An agent's own initial label is retained along its parent chain. -/
def FullHistory.initial {Input : Type} : (t : Nat) → FullHistory Input t → Bool × Input
  | 0, h => h
  | t + 1, h => initial t h.1

/-- Forget the private inputs while preserving all graph observations. -/
def FullHistory.erase {Input : Type} :
    (t : Nat) → FullHistory Input t → Counting.FullHistory t
  | 0, h => h.1
  | t + 1, h =>
      (erase t h.1, h.2.1, h.2.2.map (erase t))

noncomputable def history {Input V : Type} [Fintype V]
    (G : Nat → V → V → Nat) (leader : V → Bool) (input : V → Input) :
    (t : Nat) → V → FullHistory Input t
  | 0, x => (leader x, input x)
  | t + 1, x =>
      (history G leader input t x, ∑ y, G (t + 1) x y,
        Counting.incoming (G (t + 1)) (history G leader input t) x)

@[simp] theorem initial_history {Input V : Type} [Fintype V]
    (G : Nat → V → V → Nat) (leader : V → Bool) (input : V → Input)
    (t : Nat) (x : V) :
    FullHistory.initial t (history G leader input t x) = (leader x, input x) := by
  induction t with
  | zero => rfl
  | succ t ih => exact ih

/-- Erasure of the actual enriched history is the actual Counting history. -/
@[simp] theorem erase_history {Input V : Type} [Fintype V]
    (G : Nat → V → V → Nat) (leader : V → Bool) (input : V → Input)
    (t : Nat) (x : V) :
    FullHistory.erase t (history G leader input t x) = Counting.history G leader t x := by
  induction t generalizing x with
  | zero => rfl
  | succ t ih =>
      simp only [history, FullHistory.erase, Counting.history, Counting.incoming_map]
      simp only [ih]

/-- Evaluate a local protocol using only an enriched full-information history. -/
def Protocol.decode {Input Output State : Type} (P : Protocol Input Output State)
    (leaders : Nat) : (t : Nat) → FullHistory Input t → Status State Output
  | 0, h => .active (P.init leaders h.1 h.2)
  | t + 1, h => P.advance leaders (P.decode leaders t h.1)
      (h.2.2.filterMap (fun old => (P.decode leaders t old).message)) h.2.1

/-- Actual execution, with messages only from agents that have not halted. -/
noncomputable def Protocol.trace {Input Output State V : Type} [Fintype V]
    (P : Protocol Input Output State) (leaders : Nat) (G : Nat → V → V → Nat)
    (leader : V → Bool) (input : V → Input) : Nat → V → Status State Output
  | 0, x => .active (P.init leaders (leader x) (input x))
  | t + 1, x => P.advance leaders (P.trace leaders G leader input t x)
      ((Counting.incoming (G (t + 1))
        (P.trace leaders G leader input t) x).filterMap Status.message)
      (∑ y, G (t + 1) x y)

/-- Physical execution agrees with decoding histories, including silent halting. -/
theorem Protocol.trace_eq_decode {Input Output State V : Type} [Fintype V]
    (P : Protocol Input Output State) (leaders : Nat) (G : Nat → V → V → Nat)
    (leader : V → Bool) (input : V → Input) (t : Nat) (x : V) :
    P.trace leaders G leader input t x =
      P.decode leaders t (history G leader input t x) := by
  induction t generalizing x with
  | zero => rfl
  | succ t ih =>
      simp only [trace, history, decode]
      have hstates : P.trace leaders G leader input t =
          fun y => P.decode leaders t (history G leader input t y) := by
        funext y
        exact ih y
      rw [hstates, ← Counting.incoming_map, Multiset.filterMap_map]
      rfl

/-- Equal enriched histories force the same state and decision. -/
theorem Protocol.same_history_same_status {Input Output State V W : Type}
    [Fintype V] [Fintype W] (P : Protocol Input Output State) (leaders : Nat)
    (G : Nat → V → V → Nat) (H : Nat → W → W → Nat)
    (leaderV : V → Bool) (leaderW : W → Bool) (inputV : V → Input) (inputW : W → Input)
    (t : Nat) (x : V) (y : W)
    (h : history G leaderV inputV t x = history H leaderW inputW t y) :
    P.trace leaders G leaderV inputV t x = P.trace leaders H leaderW inputW t y := by
  rw [P.trace_eq_decode, P.trace_eq_decode, h]

/-- A halted agent remains silent and retains its output at every later time. -/
theorem Protocol.halted_forever {Input Output State V : Type} [Fintype V]
    (P : Protocol Input Output State) (leaders : Nat) (G : Nat → V → V → Nat)
    (leader : V → Bool) (input : V → Input) (t : Nat) (x : V) (s : State) (k : Output)
    (h : P.trace leaders G leader input t x = .halted s k) (d : Nat) :
    P.trace leaders G leader input (t + d) x = .halted s k := by
  induction d with
  | zero => simpa using h
  | succ d ih =>
      rw [Nat.add_succ, trace, ih]
      rfl

/-- The original Counting protocol embeds by ignoring the extra initial input. -/
def ofCounting {Input State : Type} (P : Counting.Protocol State) :
    Protocol Input Nat State where
  init leaders leader _ := P.init leaders leader
  update := P.update
  out := P.out

def ofCountingStatus {State : Type} : Counting.Status State → Status State Nat
  | .active s => .active s
  | .halted s k => .halted s k

@[simp] theorem ofCountingStatus_message {State : Type} (s : Counting.Status State) :
    (ofCountingStatus s).message = s.message := by
  cases s <;> rfl

@[simp] theorem ofCounting_advance {Input State : Type} (P : Counting.Protocol State)
    (leaders : Nat) (s : Counting.Status State) (incoming : Multiset State) (d : Nat) :
    (ofCounting (Input := Input) P).advance leaders (ofCountingStatus s) incoming d =
      ofCountingStatus (P.advance leaders s incoming d) := by
  cases s with
  | halted s k => rfl
  | active s =>
      simp only [Protocol.advance, Counting.Protocol.advance, ofCounting, ofCountingStatus]
      cases P.out (P.update s incoming d) leaders <;> rfl

/-- Ignoring inputs recovers the existing semantics exactly. -/
theorem ofCounting_decode {Input State : Type} (P : Counting.Protocol State)
    (leaders : Nat) (t : Nat) (h : FullHistory Input t) :
    (ofCounting P).decode leaders t h =
      ofCountingStatus (P.decode leaders t (FullHistory.erase t h)) := by
  induction t with
  | zero => rfl
  | succ t ih =>
      simp only [Protocol.decode, Counting.Protocol.decode, FullHistory.erase,
        Multiset.filterMap_map, ih, ofCountingStatus_message, ofCounting_advance]
      rfl

theorem ofCounting_trace {Input State V : Type} [Fintype V]
    (P : Counting.Protocol State) (leaders : Nat) (G : Nat → V → V → Nat)
    (leader : V → Bool) (input : V → Input) (t : Nat) (x : V) :
    (ofCounting P).trace leaders G leader input t x =
      ofCountingStatus (P.trace leaders G leader t x) := by
  rw [Protocol.trace_eq_decode, ofCounting_decode, erase_history,
    Counting.Protocol.trace_eq_decode]

end Counting.InputProtocol
