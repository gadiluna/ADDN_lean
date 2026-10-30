import Counting.InputProtocol

/-! A local transformation of a terminal answer needs no communication rounds.
The original state and message behavior, including silence, are preserved. -/

namespace Counting.InputProtocol

def Status.mapOutput {State A B : Type} (f : A → B) : Status State A → Status State B
  | .active s => .active s
  | .halted s a => .halted s (f a)

@[simp] theorem Status.message_mapOutput {State A B : Type} (f : A → B) (s : Status State A) :
    (s.mapOutput f).message = s.message := by
  cases s <;> rfl

def Protocol.mapOutput {Input State A B : Type} (P : Protocol Input A State) (f : A → B) :
    Protocol Input B State where
  init := P.init
  update := P.update
  out := fun s ell => (P.out s ell).map f

theorem Protocol.advance_mapOutput {Input State A B : Type} (P : Protocol Input A State)
    (f : A → B) (ell : Nat) (s : Status State A) (messages : Multiset State) (degree : Nat) :
    (P.mapOutput f).advance ell (s.mapOutput f) messages degree =
      (P.advance ell s messages degree).mapOutput f := by
  cases s with
  | halted s a => rfl
  | active s =>
    simp only [advance, mapOutput, Status.mapOutput]
    cases P.out (P.update s messages degree) ell <;> rfl

theorem Protocol.decode_mapOutput {Input State A B : Type} (P : Protocol Input A State)
    (f : A → B) (ell t : Nat) (h : FullHistory Input t) :
    (P.mapOutput f).decode ell t h = (P.decode ell t h).mapOutput f := by
  induction t with
  | zero => rfl
  | succ t ih =>
    simp only [decode, ih, Status.message_mapOutput, advance_mapOutput]

/-- Postprocessing preserves every active round and the exact first halting
round, and transforms only the terminal value. -/
theorem Protocol.trace_mapOutput {Input State A B V : Type} [Fintype V]
    (P : Protocol Input A State) (f : A → B) (ell : Nat)
    (G : Nat → V → V → Nat) (leader : V → Bool) (input : V → Input) (t : Nat) (x : V) :
    (P.mapOutput f).trace ell G leader input t x =
      (P.trace ell G leader input t x).mapOutput f := by
  rw [trace_eq_decode, trace_eq_decode, decode_mapOutput]

end Counting.InputProtocol
