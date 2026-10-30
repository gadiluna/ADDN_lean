import Counting.RealizabilityVerifier

namespace Counting.RealizabilityVerifier.Examples
open Counting.Executable

def singletonRound (multiplicity : ℕ) : Vista :=
  ⟨#[⟨0, none, true, 0, []⟩,
     ⟨1, some 0, true, multiplicity, if multiplicity = 0 then [] else [(0, multiplicity)]⟩], 1⟩

#guard verify (initialVista true) #[1] 1 1
#guard verify (initialVista true) #[1] 1 (2 ^ 64)
#guard !(verify (initialVista false) #[1] 1 1)
#guard !(verify (initialVista true) #[1] 0 1)
#guard !(verify (initialVista true) #[0] 1 1)
#guard !(verify (initialVista true) #[] 1 1)
#guard !(verify (initialVista true) #[1, 1] 1 1)
#guard verify (singletonRound 0) #[1, 1] 1 1
#guard verify (singletonRound (2 ^ 64)) #[1, 1] 1 1
#guard !(verify (singletonRound 0) #[1, 1] 1 2)

def unbalancedRound : Vista :=
  ⟨#[⟨0, none, true, 0, []⟩, ⟨1, some 0, true, 3, [(0, 2)]⟩], 1⟩

#guard !(verify unbalancedRound #[1, 1] 1 1)

def cyclicParent : Vista :=
  ⟨#[⟨0, none, true, 0, []⟩, ⟨1, some 1, true, 0, []⟩], 1⟩

#guard !(verify cyclicParent #[1, 1] 1 1)

end Counting.RealizabilityVerifier.Examples
