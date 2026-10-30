import Counting.RealizabilityPointValuesSpec
import Counting.RealizabilityMaskValuesSpec
import Counting.StackRealizabilityCountsSpec
import Counting.StackRealizabilityInitialChecked

namespace Counting.StackMachine.RealizabilityCheck
open RealizabilityVerifier RealizabilityVerifier.CompactGraph

/-- The arithmetic scan and the auxiliary graph test for one physical round.
Only the graph test is omitted for population one, exactly as in `verify`. -/
def checkedRound (vista : Executable.Vista) (weights : Array Nat) (N r : Nat) : Bool :=
  pointRangeCheck vista.nodes.toList weights.toList (vectorBits (actualFields N vista weights r).isOld)
    (r+1) N (((Executable.levelNodes vista (r+1)).map (weight weights)).sum) 0 (vista.nodes.size+1) &&
    (if 1<N then connectedCheck (roundArc N vista weights r) else true)

theorem checkedRound_iff (vista : Executable.Vista) (weights : Array Nat) (N r : Nat)
    (valid : vista.valid=true) (length : weights.size=vista.nodes.size) :
    checkedRound vista weights N r=true ↔
      (∀ u : LevelIndex vista r,childCount vista weights r u.val.val ≤ weight weights u.val.val) ∧
      (hidden N vista weights r=0 → ∀ u : LevelIndex vista r,
        supply vista weights r u.val.val=demand vista weights r u.val.val) ∧
      (0<hidden N vista weights r → ∀ u : LevelIndex vista r,leaving vista weights r u.val.val=0 →
        demand vista weights r u.val.val ≤ supply vista weights r u.val.val) ∧
      (1<N → connectedCheck (roundArc N vista weights r)=true) := by
  unfold checkedRound
  rw [Bool.and_eq_true,pointRangeCheck_verifier_component N vista weights valid length r]
  by_cases nontrivial : 1<N <;> simp [nontrivial,and_assoc]

/-- Explicit ascending scan of the depth already stored in the validated DAG. -/
def checkedRounds (vista : Executable.Vista) (weights : Array Nat) (N : Nat) : Bool :=
  (List.range (vista.node vista.bottom).level).all (checkedRound vista weights N)

theorem checkedRounds_range' (vista : Executable.Vista) (weights : Array Nat) (N : Nat) :
    (List.range' 0 (vista.node vista.bottom).level).all (checkedRound vista weights N)=
      checkedRounds vista weights N := by
  rw [←List.range_eq_range']
  rfl

theorem checkedRounds_iff (vista : Executable.Vista) (weights : Array Nat) (N : Nat)
    (valid : vista.valid=true) (length : weights.size=vista.nodes.size) :
    checkedRounds vista weights N=true ↔
      ∀ r : Fin (vista.node vista.bottom).level,
        (∀ u : LevelIndex vista r.val,childCount vista weights r.val u.val.val ≤ weight weights u.val.val) ∧
        (hidden N vista weights r.val=0 → ∀ u : LevelIndex vista r.val,
          supply vista weights r.val u.val.val=demand vista weights r.val u.val.val) ∧
        (0<hidden N vista weights r.val → ∀ u : LevelIndex vista r.val,leaving vista weights r.val u.val.val=0 →
          demand vista weights r.val u.val.val ≤ supply vista weights r.val u.val.val) ∧
        (1<N → connectedCheck (roundArc N vista weights r.val)=true) := by
  simp only [checkedRounds,List.all_eq_true,List.mem_range,checkedRound_iff vista weights N _ valid length]
  constructor
  · intro checked r
    exact checked r.val r.isLt
  · intro checked r inside
    exact checked ⟨r,inside⟩

/-- Composition target for the physical verifier. Earlier Boolean guards
supply the length and validity premises used by the later bounded scans. -/
def checkedVerifier (vista : Executable.Vista) (weights : Array Nat) (ell N : Nat) : Bool :=
  vista.valid && countsShapeCheck weights vista.nodes.size &&
    decide (weight weights vista.bottom=1) &&
    initialScanCheck vista.nodes.toList weights.toList ell N && checkedRounds vista weights N

/-- Exact total equivalence, including malformed vistas and mismatched count
arrays. No successful-validation premise escapes this theorem. -/
theorem checkedVerifier_eq (vista : Executable.Vista) (weights : Array Nat) (ell N : Nat) :
    checkedVerifier vista weights ell N=verify vista weights ell N := by
  apply Bool.eq_iff_iff.mpr
  rw [verify_iff_checks]
  constructor
  · intro accepted
    simp only [checkedVerifier,Bool.and_eq_true,decide_eq_true_eq] at accepted
    rcases accepted with ⟨⟨⟨⟨valid,shape⟩,bottom⟩,initial⟩,rounds⟩
    obtain ⟨length,positive⟩ := (countsShapeCheck_iff weights vista.nodes.size).mp shape
    rw [initialScanCheck_verifier_component vista weights ell N length,decide_eq_true_eq] at initial
    obtain ⟨leaders,order,initialLeaders,initialNonleaders⟩ := initial
    have checked := (checkedRounds_iff vista weights N valid length).mp rounds
    refine ⟨valid,length,leaders,order,positive,bottom,initialLeaders,initialNonleaders,?_,?_,?_,?_⟩
    · intro r inside
      exact (checked ⟨r,inside⟩).1
    · intro r inside
      exact (checked ⟨r,inside⟩).2.1
    · intro r inside
      exact (checked ⟨r,inside⟩).2.2.1
    · intro r inside nontrivial
      exact (connectedCheck_iff _).mp ((checked ⟨r,inside⟩).2.2.2 nontrivial)
  · intro checked
    have shape := (countsShapeCheck_iff weights vista.nodes.size).mpr ⟨checked.length,checked.positive⟩
    have initial : initialScanCheck vista.nodes.toList weights.toList ell N=true := by
      rw [initialScanCheck_verifier_component vista weights ell N checked.length,decide_eq_true_eq]
      exact ⟨checked.leaders_positive,checked.order_ge_leaders,checked.initial_leaders,checked.initial_nonleaders⟩
    have rounds : checkedRounds vista weights N=true := by
      apply (checkedRounds_iff vista weights N checked.valid checked.length).mpr
      intro r
      exact ⟨checked.refinement r.val r.isLt,checked.balance_full r.val r.isLt,
        checked.balance_no_leaving r.val r.isLt,
        fun nontrivial=>(connectedCheck_iff _).mpr (checked.connected r.val r.isLt nontrivial)⟩
    simp only [checkedVerifier,Bool.and_eq_true,decide_eq_true_eq]
    exact ⟨⟨⟨⟨checked.valid,shape⟩,checked.bottom_one⟩,initial⟩,rounds⟩

end Counting.StackMachine.RealizabilityCheck
