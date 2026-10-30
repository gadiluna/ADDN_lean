import Counting.ExternalInitialRows
import Counting.ExternalEncodingSize

namespace Counting.External.InitialRows
open Machine FiniteConstraints Cellular

theorem Setup.constraints_length {width : ℕ} (setup : Setup width) (program : Program) :
    (setup.constraints program).length ≤ width+setup.capacity*setup.capacity := by
  have pairs := flatMap_length_le (List.finRange setup.capacity)
    (fun first => ((List.finRange setup.capacity).filter (fun second => first.val+1=second.val)).map
      (setup.binary program first)) setup.capacity (by
        intro first _
        simp only [List.length_map]
        exact (List.length_filter_le _ _).trans_eq List.length_finRange)
  simpa only [Setup.constraints, List.length_append, List.length_map, List.length_finRange] using
    Nat.add_le_add_left pairs width

theorem Setup.constraints_arity {width : ℕ} (setup : Setup width) (program : Program) :
    ∀ constraint ∈ setup.constraints program, constraint.arity ≤ 2 := by
  intro constraint member
  simp only [Setup.constraints, List.mem_append, List.mem_map, List.mem_flatMap] at member
  rcases member with ⟨place, _, rfl⟩ | ⟨first, _, second, _, rfl⟩ <;>
    simp only [Setup.unary, Setup.binary, Nat.one_le_ofNat, le_refl]

def Setup.formula {width : ℕ} (setup : Setup width) (program : Program)
    (rotation : Equiv.Perm (Fin width)) (time : ℕ) :=
  Tableau.formula (T := time) (dynamics program rotation) (setup.constraints program) (accept program)

theorem Setup.formula_satisfiable_iff {width : ℕ} (setup : Setup width) (program : Program)
    (rotation : Equiv.Perm (Fin width)) (noFixed : ∀ place, rotation place ≠ place) (time : ℕ) :
    (setup.formula program rotation time).Satisfiable ↔
      ∃ witness : List Bool, witness.length ≤ setup.capacity ∧
        let final := (setup.configuration program witness).run rotation time
        program.code final.control (final.tape final.position) = none ∧ program.accept final.control = true := by
  rw [Setup.formula, Tableau.satisfiable_iff]
  constructor
  · rintro ⟨config, initial, accepted⟩
    obtain ⟨witness, bounded, rfl⟩ := (setup.constraints_exists_iff program config).mp initial
    rw [← encoded_run program rotation noFixed] at accepted
    exact ⟨witness, bounded, (exists_accept_encoded program _).mp accepted⟩
  · rintro ⟨witness, bounded, accepted⟩
    refine ⟨(setup.configuration program witness).encoded,
      (setup.constraints_exists_iff program _).mpr ⟨witness, bounded, rfl⟩, ?_⟩
    rw [← encoded_run program rotation noFixed]
    exact (exists_accept_encoded program _).mpr accepted

/-- A concrete polynomial measure for all CNF sizes. Its coefficients may
depend on the fixed verifier, through its finite alphabet. -/
def Setup.sizeBound {width : ℕ} (setup : Setup width) (program : Program) (time : ℕ) : ℕ :=
  let d := alphabet program
  let n := (time+1)*width
  let m := width+setup.capacity*setup.capacity+time*width
  n*d + n*(1+d*d)*(d+2) + m*(d^4*4) + width*d + 1

theorem Setup.formula_size_bounds {width : ℕ} (setup : Setup width) (program : Program)
    (rotation : Equiv.Perm (Fin width)) (time : ℕ) :
    ((time+1)*width)*alphabet program ≤ setup.sizeBound program time ∧
    (setup.formula program rotation time).length ≤ setup.sizeBound program time ∧
    (setup.formula program rotation time).width ≤ setup.sizeBound program time := by
  have dPositive : 0 < alphabet program := by unfold alphabet; omega
  have bounds := Tableau.size_bounds (T := time) (dynamics program rotation) (setup.constraints program)
    (accept program) 2 dPositive (setup.constraints_arity program)
  have initialBound := setup.constraints_length program
  have mBound : (setup.constraints program).length+time*width ≤
      width+setup.capacity*setup.capacity+time*width := by omega
  have lengthTerm := Nat.mul_le_mul_right ((alphabet program)^4) mBound
  have widthTerm := Nat.mul_le_mul_right ((alphabet program)^4*4) mBound
  have factor : (alphabet program)^4 ≤ (alphabet program)^4*4 := by omega
  have nTerm : ((time+1)*width)*(1+alphabet program*alphabet program) ≤
      ((time+1)*width)*(1+alphabet program*alphabet program)*(alphabet program+2) := by
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left
      (((time+1)*width)*(1+alphabet program*alphabet program))
      (show 1 ≤ alphabet program+2 by omega)
  dsimp only [Setup.formula, Setup.sizeBound]
  norm_num only [max_eq_right (show 2 ≤ 4 by omega)] at bounds
  constructor
  · omega
  · constructor
    · have more := Nat.mul_le_mul_left (width+setup.capacity*setup.capacity+time*width) factor
      omega
    · omega

theorem Setup.formula_binary_length {width : ℕ} (setup : Setup width) (program : Program)
    (rotation : Equiv.Perm (Fin width)) (time : ℕ) :
    (CNFEncoding.codec.encode ⟨((time+1)*width)*alphabet program,
      setup.formula program rotation time⟩).length ≤
      setup.sizeBound program time * (2*setup.sizeBound program time+10)+2 := by
  obtain ⟨varBound, clauseBound, occurrenceBound⟩ := setup.formula_size_bounds program rotation time
  exact CNFEncoding.input_length_polynomial _ _ varBound clauseBound occurrenceBound

end Counting.External.InitialRows
