import Counting.StackArithmeticOutput

namespace Counting.StackMachine.Arithmetic

/-- Total extension of natural addition to binary inputs. Incomplete frames
produce the canonical zero; valid frames may leave an unused suffix. -/
def additionFunction (input : List Bool) : List Bool :=
  match Encoding.unframe input with
  | none => Encoding.natural.encode 0
  | some (first, rest) => match Encoding.unframe rest with
    | none => Encoding.natural.encode 0
    | some (second, _) => Encoding.natural.encode (Encoding.value first+Encoding.value second)

theorem unframe_split {input first rest : List Bool}
    (parsed : Encoding.unframe input = some (first,rest)) : input = Encoding.frame first++rest := by
  induction input using Encoding.unframe.induct generalizing first rest with
  | case1 rest' =>
      have same : ([],rest')=(first,rest) := Option.some.inj parsed
      cases same
      rfl
  | case2 bit input ih =>
      cases inner : Encoding.unframe input with
      | none => simp [Encoding.unframe, inner] at parsed
      | some pair =>
          obtain ⟨bits,suffix⟩ := pair
          have same : (bit::bits,suffix)=(first,rest) := by
            simpa only [Encoding.unframe, inner, Option.map_some, Option.some.injEq] using parsed
          cases same
          rw [ih inner]
          rfl
  | case3 input nofalse notwo => simp [Encoding.unframe] at parsed

theorem parse_first_invalid (input output ar br a b result : List Bool)
    (invalid : Encoding.unframe input = none) :
    ∃ transitions ≤ 2*input.length+2, ∃ changed,
      Machine.run (step additionProgram) transitions (arithConfig 0 input output ar br a b result) =
        some (arithConfig 40 [] output changed br a b result) := by
  induction input using Encoding.unframe.induct generalizing ar with
  | case1 rest => simp [Encoding.unframe] at invalid
  | case2 bit input ih =>
      have invalidTail : Encoding.unframe input = none := by
        cases parsed : Encoding.unframe input with
        | none => rfl
        | some value => simp [Encoding.unframe, parsed] at invalid
      obtain ⟨transitions, bounded, changed, executed⟩ := ih (bit::ar) invalidTail
      refine ⟨3+transitions, by simp only [List.length_cons]; omega, changed, ?_⟩
      rw [Machine.run_add, parse_first_bit, Option.bind_some, executed]
  | case3 input nofalse notwo =>
      cases input with
      | nil => exact ⟨1, by simp, ar, rfl⟩
      | cons bit rest =>
          cases bit with
          | false => exact (nofalse rest rfl).elim
          | true =>
              cases rest with
              | nil => exact ⟨2, by simp, ar, by
                  apply congrArg some; apply congrArg (Config.mk _); funext r; fin_cases r <;> rfl⟩
              | cons bit rest => exact (notwo bit rest rfl).elim

theorem parse_second_invalid (input output ar br a b result : List Bool)
    (invalid : Encoding.unframe input = none) :
    ∃ transitions ≤ 2*input.length+2, ∃ changed,
      Machine.run (step additionProgram) transitions (arithConfig 5 input output ar br a b result) =
        some (arithConfig 40 [] output ar changed a b result) := by
  induction input using Encoding.unframe.induct generalizing br with
  | case1 rest => simp [Encoding.unframe] at invalid
  | case2 bit input ih =>
      have invalidTail : Encoding.unframe input = none := by
        cases parsed : Encoding.unframe input with
        | none => rfl
        | some value => simp [Encoding.unframe, parsed] at invalid
      obtain ⟨transitions, bounded, changed, executed⟩ := ih (bit::br) invalidTail
      refine ⟨3+transitions, by simp only [List.length_cons]; omega, changed, ?_⟩
      rw [Machine.run_add, parse_second_bit, Option.bind_some, executed]
  | case3 input nofalse notwo =>
      cases input with
      | nil => exact ⟨1, by simp, br, rfl⟩
      | cons bit rest =>
          cases bit with
          | false => exact (nofalse rest rfl).elim
          | true =>
              cases rest with
              | nil => exact ⟨2, by simp, br, by
                  apply congrArg some; apply congrArg (Config.mk _); funext r; fin_cases r <;> rfl⟩
              | cons bit rest => exact (notwo bit rest rfl).elim

theorem error_output (input output ar br a b result : List Bool) :
    step additionProgram (arithConfig 40 input output ar br a b result) =
      some (arithConfig 41 input (false::output) ar br a b result) := by
  apply congrArg some
  apply congrArg (Config.mk _)
  funext r
  fin_cases r <;> rfl

theorem initial_eq_arith (input : List Bool) :
    initial additionProgram input = arithConfig 0 input [] [] [] [] [] [] := by
  apply congrArg (Config.mk _)
  funext r
  fin_cases r <;> rfl

/-- The finite program halts with a linear stack-instruction bound on every
binary input, including malformed frames. -/
theorem addition_computes : ComputesIn additionProgram additionFunction (fun length => 11*length+12) := by
  intro input
  cases firstParsed : Encoding.unframe input with
  | none =>
      obtain ⟨transitions, bounded, changed, executed⟩ := parse_first_invalid input [] [] [] [] [] [] firstParsed
      refine ⟨transitions+1, arithConfig 41 [] [false] changed [] [] [] [], by dsimp; omega,
        ⟨?_, addition_halted _ _ _ _ _ _ _⟩, ?_⟩
      · rw [initial_eq_arith, Machine.run_add, executed, Option.bind_some, Machine.run, error_output, Option.bind_some]
        rfl
      · simp only [additionFunction, firstParsed]
        rfl
  | some pair =>
      obtain ⟨first, rest⟩ := pair
      have split := unframe_split firstParsed
      cases secondParsed : Encoding.unframe rest with
      | none =>
          obtain ⟨transitions, bounded, changed, executed⟩ := parse_second_invalid rest [] first.reverse [] [] [] [] secondParsed
          refine ⟨(3*first.length+1)+(transitions+1), arithConfig 41 [] [false] first.reverse changed [] [] [], ?_,
            ⟨?_, addition_halted _ _ _ _ _ _ _⟩, ?_⟩
          · have length : input.length = 2*first.length+1+rest.length := by rw [split, List.length_append, Encoding.frame_length]
            dsimp
            omega
          · rw [initial_eq_arith, split, Machine.run_add, parse_first, Option.bind_some, List.append_nil,
              Machine.run_add, executed, Option.bind_some, Machine.run, error_output, Option.bind_some]
            rfl
          · simp only [additionFunction, firstParsed, secondParsed]
            rfl
      | some pair =>
          obtain ⟨second, suffix⟩ := pair
          have splitSecond := unframe_split secondParsed
          obtain ⟨transitions, bounded, halted⟩ := addition_frames first second suffix
          refine ⟨transitions, arithConfig 41 suffix (Encoding.natural.encode (Encoding.value first+Encoding.value second)) [] [] [] [] [], ?_, ?_, ?_⟩
          · have length : first.length+second.length ≤ input.length := by
              rw [split, splitSecond, List.length_append, List.length_append, Encoding.frame_length, Encoding.frame_length]
              omega
            dsimp
            omega
          · simpa only [split, splitSecond, List.append_assoc] using halted
          · simp only [additionFunction, firstParsed, secondParsed]
            rfl

end Counting.StackMachine.Arithmetic
