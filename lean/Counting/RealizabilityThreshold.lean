import Counting.RealizabilitySpectrum

namespace Counting.Realizability
open TimingProtocolLocal

/-- The same selected counts pass at every order at least K+ell+1;
K is the intrinsic causal-support bound of the input vista. -/
theorem Certificate.at_support_threshold {ell N t : Nat} {H : FullHistory t} {k : Counts}
    (cert : Certificate ell N t H k)
    (openSupport : (∑ u ∈ levels t H 0, k 0 u) < N)
    (bound : (∑ u ∈ levels t H 0, k 0 u) ≤ supportBound ell t H)
    (N' : Nat) (large : supportBound ell t H + ell + 1 ≤ N') : Certificate ell N' t H k := by
  apply cert.at_open_order openSupport N'
  · omega
  · have initial := initial_total_eq (H := H) (k := k)
    omega
  · omega

end Counting.Realizability
