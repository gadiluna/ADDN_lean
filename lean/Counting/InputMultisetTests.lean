import Counting.InputMultisetLocal

/-! Direct reconstruction checks. The expected answers are the original
input lists, independent of the history or reconstruction implementation. -/

namespace Counting.InputMultisetTests
open scoped BigOperators

def finiteHistory {n : Nat} (G : Nat → Fin n → Fin n → Nat)
    (leader : Fin n → Bool) (input : Fin n → Nat) :
    (t : Nat) → Fin n → InputProtocol.FullHistory Nat t
  | 0, x => (leader x, input x)
  | t + 1, x =>
      (finiteHistory G leader input t x, ∑ y, G (t + 1) x y,
        ∑ y, Multiset.replicate (G (t + 1) y x) (finiteHistory G leader input t y))

def cycle {n : Nat} (_t : Nat) (x y : Fin n) : Nat :=
  if (x.val + 1) % n = y.val then 1 else 0

def changingThree (t : Nat) (x y : Fin 3) : Nat :=
  if t % 2 = 0 then
    if (y.val + 1) % 3 = x.val then 1 else 0
  else if x = y then 1 else 2

def check {n : Nat} (name : String) (G : Nat → Fin n → Fin n → Nat)
    (leader : Fin n → Bool) (input : Fin n → Nat) (depth : Nat) : IO Unit := do
  let expected := (Finset.univ : Finset (Fin n)).val.map input
  for x in List.finRange n do
    let actual := InputMultisetLocal.recover n depth (finiteHistory G leader input depth x)
    unless actual = some expected do
      throw (IO.userError s!"Input multiset reconstruction failed: {name}, observer {x.val}")

def main : IO Unit := do
  check (n := 1) "singleton, depth zero" (fun _ _ _ => 0) (fun _ => true) (fun _ => 17) 0
  check (n := 1) "singleton, loops" (fun _ _ _ => 3) (fun _ => true) (fun _ => 17) 1
  check (n := 2) "two different inputs, all leaders" cycle (fun _ => true) (fun x => x.val + 8) 2
  check (n := 2) "two equal inputs, one leader" cycle (fun x => x.val == 0) (fun _ => 8) 3
  check (n := 3) "three equal inputs" cycle (fun x => x.val == 0) (fun _ => 4) 4
  check (n := 3) "repeated input, all leaders" cycle (fun _ => true) (fun x => x.val % 2) 4
  check (n := 3) "three distinct inputs, two leaders" cycle (fun x => x.val < 2) (fun x => x.val + 20) 4
  check (n := 3) "changing multigraph, repeated input" changingThree
    (fun x => x.val < 2) (fun x => x.val % 2) 4
  IO.println "Input multiset tests passed (8 networks, every observer; singleton, repeated and distinct inputs, leaders, loops and changing parallel arcs)."

#eval main

end Counting.InputMultisetTests
