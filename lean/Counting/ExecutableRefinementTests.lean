import Counting.ExecutableRefinementEquivalence

namespace Counting.Executable
open Counting.TimingProtocolLocal

/-- The audit's meaning for a concrete network history, preserving the
physical round and the exact decoded vista. -/
theorem audit_actual_iff_pass {V : Type} [Fintype V]
    (G : Nat → V → V → Nat) (leader : V → Bool) (ell candidate final depth : Nat)
    (receiver : V) (vista : Vista) (valid : vista.valid = true)
    (level : (vista.node vista.bottom).level = depth)
    (history : decodeNode vista depth vista.bottom = Counting.history G leader depth receiver)
    (within : final ≤ depth) :
    (audit? vista ell candidate final).isSome = true ↔
      Pass ell candidate final depth (Counting.history G leader depth receiver) := by
  subst depth
  simpa only [Vista.denotes, history] using audit_isSome_iff_pass vista valid ell candidate final within

theorem core_audit_reject_lt {V : Type} [Fintype V]
    (G : Nat → V → V → Nat) (leader : V → Bool) (ell candidate depth : Nat)
    (network : Counting.Admissible ell G leader) (receiver : V) (vista : Vista)
    (valid : vista.valid = true) (level : (vista.node vista.bottom).level = depth)
    (history : decodeNode vista depth vista.bottom = Counting.history G leader depth receiver)
    (within : candidate ≤ depth) (small : candidate < Fintype.card V) :
    audit? vista ell candidate candidate = none := by
  cases result : audit? vista ell candidate candidate with
  | none => rfl
  | some witness =>
      have pass := (audit_actual_iff_pass G leader ell candidate candidate depth receiver vista valid level history within).mp
        (by simp [result])
      have equal := core_pass_sound G leader ell candidate depth receiver network within pass
      omega

theorem core_audit_accept_true {V : Type} [Fintype V]
    (G : Nat → V → V → Nat) (leader : V → Bool) (ell : Nat)
    (network : Counting.Admissible ell G leader) (receiver : V) (vista : Vista)
    (valid : vista.valid = true)
    (level : (vista.node vista.bottom).level = 2 * Fintype.card V - 1)
    (history : decodeNode vista (2 * Fintype.card V - 1) vista.bottom =
      Counting.history G leader (2 * Fintype.card V - 1) receiver) :
    (audit? vista ell (Fintype.card V) (Fintype.card V)).isSome = true := by
  have positive : 0 < Fintype.card V := lt_of_lt_of_le network.positive network.leaderCount_le_card
  apply (audit_actual_iff_pass G leader ell _ _ _ receiver vista valid level history (by omega)).mpr
  exact true_core_pass G leader ell receiver network

theorem short_audit_reject_lt {V : Type} [Fintype V]
    (G : Nat → V → V → Nat) (leader : V → Bool) (ell candidate : Nat)
    (network : Counting.Admissible ell G leader) (receiver : V) (vista : Vista)
    (valid : vista.valid = true) (level : (vista.node vista.bottom).level = 2 * candidate - 2)
    (history : decodeNode vista (2 * candidate - 2) vista.bottom =
      Counting.history G leader (2 * candidate - 2) receiver)
    (many : 2 ≤ ell) (larger : ell < candidate) (small : candidate < Fintype.card V) :
    audit? vista ell candidate (candidate - 1) = none := by
  cases result : audit? vista ell candidate (candidate - 1) with
  | none => rfl
  | some witness =>
      have pass := (audit_actual_iff_pass G leader ell candidate (candidate - 1) _ receiver vista valid level history
        (by omega)).mp (by simp [result])
      exact False.elim (false_short_pass G leader ell candidate receiver network many larger small pass)

theorem short_audit_accept_true {V : Type} [Fintype V]
    (G : Nat → V → V → Nat) (leader : V → Bool) (ell : Nat)
    (network : Counting.Admissible ell G leader) (receiver : V) (vista : Vista)
    (valid : vista.valid = true)
    (level : (vista.node vista.bottom).level = 2 * Fintype.card V - 2)
    (history : decodeNode vista (2 * Fintype.card V - 2) vista.bottom =
      Counting.history G leader (2 * Fintype.card V - 2) receiver)
    (nonleaders : ell < Fintype.card V) :
    (audit? vista ell (Fintype.card V) (Fintype.card V - 1)).isSome = true := by
  have positive := network.positive
  apply (audit_actual_iff_pass G leader ell _ _ _ receiver vista valid level history (by omega)).mpr
  exact true_short_pass G leader ell receiver network nonleaders

end Counting.Executable
