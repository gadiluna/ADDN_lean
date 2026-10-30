import Counting.MachineCountingRuntimeInput
import Counting.ExecutableRefinementCorePhysical

namespace Counting.StackMachine.ProtocolAdvance
open Executable
open scoped BigOperators

private theorem optimizedTime_le_twice (population leaders : Nat) :
    Counting.TimingProtocol.optimizedTime population leaders ≤ 2*population := by
  unfold Counting.TimingProtocol.optimizedTime
  split
  · omega
  · split <;> omega

/-- Instantiate the codec bound on the actual live optimized network run,
including its silent-send convention. -/
theorem binary_network_input_bound {V : Type} [Fintype V]
    (G : Nat → V → V → Nat) (leader : V → Bool) (ell M : Nat)
    (network : Counting.Admissible ell G leader) (depth : Nat)
    (before : depth < Counting.TimingProtocol.optimizedTime (Fintype.card V) ell)
    (mass : ∀ r,0 < r → r ≤ 2*Fintype.card V → arcMass G r ≤ M) (receiver : V) :
    (inputWord (binaryNetworkRun G leader ell depth receiver)
      (activePhysicalBundles (G (depth+1)) (binaryNetworkRun G leader ell depth) receiver)
      (∑ sender,G (depth+1) receiver sender)).length+1 ≤
      4000*(Fintype.card V+M.size+1)^6 := by
  have previous := binary_network_before G leader ell network depth before
  have active := fun sender=>(previous sender).2
  have horizon := optimizedTime_le_twice (Fintype.card V) ell
  rw [activePhysicalBundles_of_active _ _ active]
  apply physical_inputWord_horizon G leader ell depth M (binaryNetworkRun G leader ell depth)
    (fun sender=>(previous sender).1) receiver (active receiver) network.leaderCount_le_card (by omega)
  intro r pos within
  exact mass r pos (by omega)

/-- The original core Counting run has the same compact physical interface
and the same population-and-label polynomial. -/
theorem binary_core_network_input_bound {V : Type} [Fintype V]
    (G : Nat → V → V → Nat) (leader : V → Bool) (ell M : Nat)
    (network : Counting.Admissible ell G leader) (depth : Nat)
    (before : depth < 2*Fintype.card V-1)
    (mass : ∀ r,0 < r → r ≤ 2*Fintype.card V → arcMass G r ≤ M) (receiver : V) :
    (inputWord (binaryCoreNetworkRun G leader ell depth receiver)
      (activePhysicalBundles (G (depth+1)) (binaryCoreNetworkRun G leader ell depth) receiver)
      (∑ sender,G (depth+1) receiver sender)).length+1 ≤
      4000*(Fintype.card V+M.size+1)^6 := by
  have previous := binary_core_network_before G leader ell network depth before
  have active := fun sender=>(previous sender).2
  rw [activePhysicalBundles_of_active _ _ active]
  apply physical_inputWord_horizon G leader ell depth M (binaryCoreNetworkRun G leader ell depth)
    (fun sender=>(previous sender).1) receiver (active receiver) network.leaderCount_le_card (by omega)
  intro r pos within
  exact mass r pos (by omega)

end Counting.StackMachine.ProtocolAdvance
