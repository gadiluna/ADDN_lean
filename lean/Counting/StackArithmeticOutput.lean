import Counting.StackArithmeticParse

namespace Counting.StackMachine.Arithmetic

def frameBody (bits : List Bool) : List Bool := bits.flatMap (fun bit => [true,bit])

theorem frame_eq_body (bits : List Bool) : Encoding.frame bits = frameBody bits++[false] := by
  induction bits with
  | nil => rfl
  | cons bit bits ih => simp only [Encoding.frame, ih, frameBody, List.flatMap_cons, List.cons_append, List.nil_append]

theorem frameBody_append (first second : List Bool) :
    frameBody (first++second) = frameBody first++frameBody second := List.flatMap_append

theorem normalize_append_false (bits : List Bool) : normalize (bits++[false]) = normalize bits := by
  induction bits with
  | nil => rfl
  | cons bit bits ih => simp only [List.cons_append, normalize, ih]

theorem normalize_append_true (bits : List Bool) : normalize (bits++[true]) = bits++[true] := by
  induction bits with
  | nil => rfl
  | cons bit bits ih =>
      simp only [List.cons_append, normalize, ih]
      rw [if_neg (by simp)]

theorem output_bit (bit : Bool) (input output ar br a b result : List Bool) :
    Machine.run (step additionProgram) 3 (arithConfig 39 input output ar br a b (bit::result)) =
      some (arithConfig 39 input (true::bit::output) ar br a b result) := by
  cases bit <;> apply congrArg some <;> apply congrArg (Config.mk _) <;>
    funext r <;> fin_cases r <;> rfl

theorem output_end (input output ar br a b : List Bool) :
    step additionProgram (arithConfig 39 input output ar br a b []) =
      some (arithConfig 41 input output ar br a b []) := by
  apply congrArg some
  apply congrArg (Config.mk _)
  funext r
  fin_cases r <;> rfl

theorem output_run (input output ar br a b result : List Bool) :
    Machine.run (step additionProgram) (3*result.length+1) (arithConfig 39 input output ar br a b result) =
      some (arithConfig 41 input (frameBody result.reverse++output) ar br a b []) := by
  induction result generalizing output with
  | nil =>
      rw [show 3*([].length)+1=1 by rfl, Machine.run, output_end, Option.bind_some]
      rfl
  | cons bit result ih =>
      rw [List.length_cons, show 3*(result.length+1)+1=3+(3*result.length+1) by omega,
        Machine.run_add, output_bit, Option.bind_some, ih]
      rw [List.reverse_cons, frameBody_append]
      simp only [frameBody, List.flatMap_cons, List.flatMap_nil, List.append_assoc,
        List.cons_append, List.nil_append]

theorem strip_false (input output ar br a b result : List Bool) :
    step additionProgram (arithConfig 35 input output ar br a b (false::result)) =
      some (arithConfig 35 input output ar br a b result) := by
  apply congrArg some
  apply congrArg (Config.mk _)
  funext r
  fin_cases r <;> rfl

theorem strip_true (input output ar br a b result : List Bool) :
    Machine.run (step additionProgram) 3 (arithConfig 35 input output ar br a b (true::result)) =
      some (arithConfig 39 input (true::true::output) ar br a b result) := by
  apply congrArg some
  apply congrArg (Config.mk _)
  funext r
  fin_cases r <;> rfl

theorem strip_end (input output ar br a b : List Bool) :
    step additionProgram (arithConfig 35 input output ar br a b []) =
      some (arithConfig 41 input output ar br a b []) := by
  apply congrArg some
  apply congrArg (Config.mk _)
  funext r
  fin_cases r <;> rfl

/-- The executed strip loop removes precisely the redundant high zero bits. -/
theorem strip_run (input ar br a b result : List Bool) :
    ∃ transitions ≤ 3*result.length+1,
      Machine.run (step additionProgram) transitions (arithConfig 35 input [false] ar br a b result) =
        some (arithConfig 41 input (Encoding.frame (normalize result.reverse)) ar br a b []) := by
  induction result with
  | nil =>
      refine ⟨1, le_rfl, ?_⟩
      rw [Machine.run, strip_end, Option.bind_some]
      rfl
  | cons bit result ih =>
      cases bit with
      | false =>
          obtain ⟨transitions, bounded, executed⟩ := ih
          refine ⟨transitions+1, by simp only [List.length_cons]; omega, ?_⟩
          rw [Machine.run, strip_false, Option.bind_some, executed,
            List.reverse_cons, normalize_append_false]
      | true =>
          refine ⟨3+(3*result.length+1), by simp only [List.length_cons]; omega, ?_⟩
          rw [Machine.run_add, strip_true, Option.bind_some, output_run,
            List.reverse_cons, normalize_append_true, frame_eq_body, frameBody_append]
          simp only [frameBody, List.flatMap_cons, List.flatMap_nil, List.append_assoc,
            List.cons_append, List.nil_append]

theorem format_run (input ar br a b result : List Bool) :
    ∃ transitions ≤ 3*result.length+2,
      Machine.run (step additionProgram) transitions (arithConfig 34 input [] ar br a b result) =
        some (arithConfig 41 input (Encoding.frame (normalize result.reverse)) ar br a b []) := by
  obtain ⟨transitions, bounded, executed⟩ := strip_run input ar br a b result
  refine ⟨transitions+1, by omega, ?_⟩
  have start : step additionProgram (arithConfig 34 input [] ar br a b result) =
      some (arithConfig 35 input [false] ar br a b result) := by
    apply congrArg some
    apply congrArg (Config.mk _)
    funext r
    fin_cases r <;> rfl
  rw [Machine.run, start, Option.bind_some, executed]

theorem addition_halted (input output ar br a b result : List Bool) :
    step additionProgram (arithConfig 41 input output ar br a b result) = none := rfl

/-- A complete addition run over the actual two self-delimiting bit frames.
No canonical-input assumption is needed; the output is canonical. -/
theorem addition_frames (first second suffix : List Bool) :
    ∃ transitions ≤ 11*(first.length+second.length)+12,
      HaltsAt additionProgram (Encoding.frame first++Encoding.frame second++suffix) transitions
        (arithConfig 41 suffix (Encoding.natural.encode (Encoding.value first+Encoding.value second)) [] [] [] [] []) := by
  obtain ⟨carrySteps, carryBound, carryRun⟩ := carry_loop suffix [] [] [] first second []
  obtain ⟨outputSteps, outputBound, outputRun⟩ :=
    format_run suffix [] [] [] [] (addBits false first second).reverse
  simp only [List.length_reverse, List.reverse_reverse] at outputBound outputRun
  have sumLength := addBits_length false first second
  refine ⟨(5*(first.length+second.length)+4)+(carrySteps+outputSteps), by omega,
    ⟨?_, addition_halted _ _ _ _ _ _ _⟩⟩
  rw [Machine.run_add, parse_pair, Option.bind_some, Machine.run_add,
    carryRun, Option.bind_some, List.append_nil, outputRun]
  have encoded : Encoding.frame (normalize (addBits false first second)) =
      Encoding.natural.encode (Encoding.value first+Encoding.value second) := by
    rw [normalize_eq_bits, addBits_value]
    rfl
  rw [encoded]

theorem addition_naturals (first second : Nat) :
    ∃ transitions ≤ 11*(first.size+second.size)+12,
      HaltsAt additionProgram ((Encoding.product Encoding.natural Encoding.natural).encode (first,second)) transitions
        (arithConfig 41 [] (Encoding.natural.encode (first+second)) [] [] [] [] []) := by
  simpa only [Encoding.product, Encoding.natural, List.append_nil, Encoding.value_bits, Encoding.bits_length] using
    addition_frames first.bits second.bits []

end Counting.StackMachine.Arithmetic
