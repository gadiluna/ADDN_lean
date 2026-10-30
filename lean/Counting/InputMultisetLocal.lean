import Counting.InputProtocol
import Mathlib.Data.Finset.Pi
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Multiset.UnionInter

/-! A finite, executable input-multiset extractor. The only parameters are the
known population and the agent's own enriched history. Bounded search replaces
linear solving; the union of all successful outputs avoids choosing an element
of an unordered finite set. Correctness shows that those outputs agree. -/

namespace Counting.InputMultisetLocal
open InputProtocol
open scoped BigOperators

variable {Input : Type} [DecidableEq Input]

instance historyDecidableEq : (r : Nat) → DecidableEq (InputProtocol.FullHistory Input r)
  | 0 => inferInstanceAs (DecidableEq (Bool × Input))
  | r + 1 => by
      letI := historyDecidableEq r
      exact inferInstanceAs (DecidableEq
        (InputProtocol.FullHistory Input r × Nat × Multiset (InputProtocol.FullHistory Input r)))

def occurrences (r : Nat) : (d : Nat) → InputProtocol.FullHistory Input (r + d) → Finset (InputProtocol.FullHistory Input r)
  | 0, h => {h}
  | d + 1, h => occurrences r d h.1 ∪ h.2.2.toFinset.biUnion (occurrences r d)

def levels (t : Nat) (H : InputProtocol.FullHistory Input t) (r : Nat) : Finset (InputProtocol.FullHistory Input r) :=
  if hr : r ≤ t then occurrences r (t - r)
    (cast (congrArg (InputProtocol.FullHistory Input) (Nat.add_sub_of_le hr).symm) H) else ∅

def weightAt {r : Nat} (s : Finset (InputProtocol.FullHistory Input r))
    (w : ∀ h ∈ s, Nat) (h : InputProtocol.FullHistory Input r) : Nat :=
  if hh : h ∈ s then w h hh else 0

def Valid (n r : Nat) (s : Finset (InputProtocol.FullHistory Input (r + 1)))
    (w : ∀ h ∈ s, Nat) : Prop :=
  (∀ i ∈ s, ∀ j ∈ s, i.1 = j.1 → i = j) ∧
  (∑ i ∈ s, weightAt s w i) = n ∧
  (∀ i ∈ s, (∑ j ∈ s, j.2.2.count i.1 * weightAt s w j) =
    i.2.1 * weightAt s w i)

instance validDecidable (n r : Nat) (s : Finset (InputProtocol.FullHistory Input (r + 1)))
    (w : ∀ h ∈ s, Nat) : Decidable (Valid n r s w) := by
  unfold Valid
  infer_instance

def solutions (n r : Nat) (s : Finset (InputProtocol.FullHistory Input (r + 1))) :
    Finset (∀ h ∈ s, Nat) :=
  (s.pi (fun _ => Finset.range (n + 1))).filter (Valid n r s)

def candidateOutput (r : Nat) (s : Finset (InputProtocol.FullHistory Input (r + 1)))
    (w : ∀ h ∈ s, Nat) : Multiset Input :=
  ∑ h ∈ s, Multiset.replicate (weightAt s w h) (InputProtocol.FullHistory.initial (r + 1) h).2

def atRound (n r : Nat) (s : Finset (InputProtocol.FullHistory Input (r + 1))) : Multiset Input :=
  (solutions n r s).sup (candidateOutput r s)

def reconstruction (n t : Nat) (H : InputProtocol.FullHistory Input t) : Multiset Input :=
  (Finset.range (n - 1)).sup (fun r => atRound n r (levels t H (r + 1)))

/-- No network, identities, actual population, fibers, or anonymity data are
available to this local program. Input equality is the only input operation. -/
def recover (n t : Nat) (H : InputProtocol.FullHistory Input t) : Option (Multiset Input) :=
  if ∀ h ∈ levels t H 0, h.2 = (InputProtocol.FullHistory.initial t H).2 then
    some (Multiset.replicate n (InputProtocol.FullHistory.initial t H).2)
  else
    let result := reconstruction n t H
    if result.card = n then some result else none

end Counting.InputMultisetLocal
