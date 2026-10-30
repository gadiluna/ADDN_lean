import Counting.StackGaussianPivotInput
import Counting.StackGaussianPivotOutput

namespace Counting.StackMachine.GaussianPivot
open DirectedCounting.VerifiedGaussianAnchorSolver RationalSystem Routine

abbrev complete : Routine 29 := sequence prepareInput (sequence loop formatResult)

theorem search_index_le (value : Nat → Rat) (count start : Nat) :
    (search value count start).1 ≤ start+count := by
  induction count generalizing start with
  | zero => simp [search]
  | succ count ih =>
    by_cases zero : value start=0
    · simpa only [search,if_pos zero,show start+(count+1)=start+1+count by omega] using ih (start+1)
    · simp [search,zero]

theorem matrix_row_count_le (rows : List (List Rat)) :
    rows.length ≤ (Encoding.rationalMatrix.encode rows).length := by
  have fields : ∀ values : List (List Rat), values.length ≤ (Encoding.sequence (Encoding.framed Encoding.rationalRow) values).length := by
    intro values
    induction values with
    | nil => rfl
    | cons value values ih =>
      simp only [Encoding.sequence,Encoding.framed_length,List.length_append,List.length_cons]
      omega
  have bounded := fields rows
  change rows.length ≤ (Encoding.frame rows.length.bits++Encoding.sequence (Encoding.framed Encoding.rationalRow) rows).length
  simp only [List.length_append]
  omega

/-- Complete canonical-input pivot search, including binary-header parsing,
construction of the candidate counters, all coefficient reads, and binary
serialization of the optional result. -/
theorem complete_halts {q : Nat} (system : RationalSystem q) (pivot : Fin q) :
    ∃ steps output,
      steps  ≤  50000*((inputWord (StoredGaussian.augmentedMatrix system) pivot.val).length+1)^3 ∧
      HaltsAt complete.program (inputWord (StoredGaussian.augmentedMatrix system) pivot.val) steps output ∧
      output.store 1=Encoding.optionalNatural.encode ((findPivot? system pivot).map Fin.val) := by
  let rows := StoredGaussian.augmentedMatrix system
  let matrix := Encoding.rationalMatrix.encode rows
  let input := inputWord rows pivot.val
  let found := search (columnValue system pivot) (q-pivot.val) pivot.val
  obtain ⟨prepareTime,prepareBound,prepared⟩ := prepareInput_executes rows pivot.val
  obtain ⟨loopTime,loopBound,searched⟩ := loop_executes rows pivot.val (columnValue system pivot)
    (augmented_entries system pivot) (q-pivot.val) pivot.val (by simp [rows])
  simp only [rows,StoredGaussian.augmentedMatrix_length] at prepared loopBound
  obtain ⟨formatTime,formatBound,formatted⟩ := formatResult_executes matrix found.1 pivot.val found.2
  have exactResult : (if found.2 then none else some found.1)=(findPivot? system pivot).map Fin.val :=
    searchResult_findPivot system pivot
  rw [exactResult] at formatted
  obtain ⟨finish,ran,halted,stored⟩ := prepared.sequence (searched.sequence formatted)
  have countBound : q ≤ matrix.length := by simpa [rows] using matrix_row_count_le rows
  have inputLength : input.length=2*pivot.val+1+matrix.length := by simp [input,inputWord,Encoding.frame_length,matrix]
  have indexBound : found.1 ≤ q := by
    have bounded := search_index_le (columnValue system pivot) (q-pivot.val) pivot.val
    change found.1 ≤ pivot.val+(q-pivot.val) at bounded
    omega
  have candidateBound : q-pivot.val ≤ input.length := by omega
  have baseBound : matrix.length+q+pivot.val+(q-pivot.val)+7 ≤ 7*(input.length+1) := by omega
  have loopLimit : loopTime ≤ 40000*(input.length+1)^2 := by
    apply loopBound.trans
    change (q-pivot.val)*(5000*(matrix.length+q+pivot.val+(q-pivot.val)+7)+2)+1 ≤ _
    calc
      _  ≤  input.length*(5000*(7*(input.length+1))+2)+1 := by gcongr
      _  ≤  _ := by nlinarith
  have formatLimit : formatTime ≤ 80*(input.length+1)^2 := by
    apply formatBound.trans
    calc
      _  ≤ 20*(2*(input.length+1))^2 := by gcongr;omega
      _ = _ := by ring
  have quadratic : (input.length+1)^2 ≤ (input.length+1)^3 := by
    calc
      _  ≤ (input.length+1)^2*(input.length+1) := Nat.le_mul_of_pos_right _ (by omega)
      _ = _ := by ring
  refine ⟨prepareTime+1+(loopTime+1+formatTime),finish,?_,⟨?_,halted⟩,?_⟩
  · change prepareTime ≤ 2000*(input.length+1)^3 at prepareBound
    change _  ≤ 50000*(input.length+1)^3
    have positive := Nat.one_le_pow' 3 input.length
    omega
  · have start : initial complete.program input=⟨0,seed input [] []⟩ := by
      apply congrArg (Config.mk _)
      funext r;fin_cases r <;> simp [file]
    rw [start]
    exact ran
  · rw [stored]
    rfl

end Counting.StackMachine.GaussianPivot
