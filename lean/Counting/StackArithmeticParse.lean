import Counting.StackArithmeticProgram

namespace Counting.StackMachine.Arithmetic

/-- Explicit registers at every phase of the same 42-state program. -/
def arithConfig (state : Control additionProgram)
    (input output firstRev secondRev first second result : List Bool) : Config additionProgram :=
  ⟨state, fun r => match r.val with
    | 0 => input | 1 => output | 2 => firstRev | 3 => secondRev
    | 4 => first | 5 => second | _ => result⟩

theorem parse_first_bit (bit : Bool) (input output ar br a b result : List Bool) :
    Machine.run (step additionProgram) 3
      (arithConfig 0 (true::bit::input) output ar br a b result) =
      some (arithConfig 0 input output (bit::ar) br a b result) := by
  cases bit <;> apply congrArg some <;> apply congrArg (Config.mk _) <;>
    funext r <;> fin_cases r <;> rfl

theorem parse_first_end (input output ar br a b result : List Bool) :
    step additionProgram (arithConfig 0 (false::input) output ar br a b result) =
      some (arithConfig 5 input output ar br a b result) := by
  apply congrArg some
  apply congrArg (Config.mk _)
  funext r
  fin_cases r <;> rfl

theorem parse_first (bits suffix output ar br a b result : List Bool) :
    Machine.run (step additionProgram) (3*bits.length+1)
      (arithConfig 0 (Encoding.frame bits++suffix) output ar br a b result) =
      some (arithConfig 5 suffix output (bits.reverse++ar) br a b result) := by
  induction bits generalizing ar with
  | nil =>
      rw [show 3*([].length)+1=1 by rfl, Machine.run]
      change (step additionProgram (arithConfig 0 (false::suffix) output ar br a b result)).bind _ = _
      rw [parse_first_end, Option.bind_some]
      rfl
  | cons bit bits ih =>
      rw [List.length_cons, show 3*(bits.length+1)+1=3+(3*bits.length+1) by omega,
        Machine.run_add]
      simp only [Encoding.frame, List.cons_append]
      rw [parse_first_bit, Option.bind_some, ih]
      simp only [List.reverse_cons, List.append_assoc, List.singleton_append]

theorem parse_second_bit (bit : Bool) (input output ar br a b result : List Bool) :
    Machine.run (step additionProgram) 3
      (arithConfig 5 (true::bit::input) output ar br a b result) =
      some (arithConfig 5 input output ar (bit::br) a b result) := by
  cases bit <;> apply congrArg some <;> apply congrArg (Config.mk _) <;>
    funext r <;> fin_cases r <;> rfl

theorem parse_second_end (input output ar br a b result : List Bool) :
    step additionProgram (arithConfig 5 (false::input) output ar br a b result) =
      some (arithConfig 10 input output ar br a b result) := by
  apply congrArg some
  apply congrArg (Config.mk _)
  funext r
  fin_cases r <;> rfl

theorem parse_second (bits suffix output ar br a b result : List Bool) :
    Machine.run (step additionProgram) (3*bits.length+1)
      (arithConfig 5 (Encoding.frame bits++suffix) output ar br a b result) =
      some (arithConfig 10 suffix output ar (bits.reverse++br) a b result) := by
  induction bits generalizing br with
  | nil =>
      rw [show 3*([].length)+1=1 by rfl, Machine.run]
      change (step additionProgram (arithConfig 5 (false::suffix) output ar br a b result)).bind _ = _
      rw [parse_second_end, Option.bind_some]
      rfl
  | cons bit bits ih =>
      rw [List.length_cons, show 3*(bits.length+1)+1=3+(3*bits.length+1) by omega,
        Machine.run_add]
      simp only [Encoding.frame, List.cons_append]
      rw [parse_second_bit, Option.bind_some, ih]
      simp only [List.reverse_cons, List.append_assoc, List.singleton_append]

theorem restore_first_bit (bit : Bool) (input output ar br a b result : List Bool) :
    Machine.run (step additionProgram) 2 (arithConfig 10 input output (bit::ar) br a b result) =
      some (arithConfig 10 input output ar br (bit::a) b result) := by
  cases bit <;> apply congrArg some <;> apply congrArg (Config.mk _) <;>
    funext r <;> fin_cases r <;> rfl

theorem restore_first_end (input output br a b result : List Bool) :
    step additionProgram (arithConfig 10 input output [] br a b result) =
      some (arithConfig 14 input output [] br a b result) := by
  apply congrArg some
  apply congrArg (Config.mk _)
  funext r
  fin_cases r <;> rfl

theorem restore_first (input output ar br a b result : List Bool) :
    Machine.run (step additionProgram) (2*ar.length+1) (arithConfig 10 input output ar br a b result) =
      some (arithConfig 14 input output [] br (ar.reverse++a) b result) := by
  induction ar generalizing a with
  | nil =>
      rw [show 2*([].length)+1=1 by rfl, Machine.run, restore_first_end, Option.bind_some]
      rfl
  | cons bit ar ih =>
      rw [List.length_cons, show 2*(ar.length+1)+1=2+(2*ar.length+1) by omega,
        Machine.run_add, restore_first_bit, Option.bind_some, ih]
      simp only [List.reverse_cons, List.append_assoc, List.singleton_append]

theorem restore_second_bit (bit : Bool) (input output ar br a b result : List Bool) :
    Machine.run (step additionProgram) 2 (arithConfig 14 input output ar (bit::br) a b result) =
      some (arithConfig 14 input output ar br a (bit::b) result) := by
  cases bit <;> apply congrArg some <;> apply congrArg (Config.mk _) <;>
    funext r <;> fin_cases r <;> rfl

theorem restore_second_end (input output ar a b result : List Bool) :
    step additionProgram (arithConfig 14 input output ar [] a b result) =
      some (arithConfig 18 input output ar [] a b result) := by
  apply congrArg some
  apply congrArg (Config.mk _)
  funext r
  fin_cases r <;> rfl

theorem restore_second (input output ar br a b result : List Bool) :
    Machine.run (step additionProgram) (2*br.length+1) (arithConfig 14 input output ar br a b result) =
      some (arithConfig 18 input output ar [] a (br.reverse++b) result) := by
  induction br generalizing b with
  | nil =>
      rw [show 2*([].length)+1=1 by rfl, Machine.run, restore_second_end, Option.bind_some]
      rfl
  | cons bit br ih =>
      rw [List.length_cons, show 2*(br.length+1)+1=2+(2*br.length+1) by omega,
        Machine.run_add, restore_second_bit, Option.bind_some, ih]
      simp only [List.reverse_cons, List.append_assoc, List.singleton_append]

theorem parse_pair (first second suffix : List Bool) :
    Machine.run (step additionProgram) (5*(first.length+second.length)+4)
      (initial additionProgram (Encoding.frame first++Encoding.frame second++suffix)) =
      some (arithConfig 18 suffix [] [] [] first second []) := by
  have start : initial additionProgram (Encoding.frame first++Encoding.frame second++suffix) =
      arithConfig 0 (Encoding.frame first++(Encoding.frame second++suffix)) [] [] [] [] [] [] := by
    apply congrArg (Config.mk _)
    funext r
    fin_cases r <;> simp [List.append_assoc]
  have time : 5*(first.length+second.length)+4 =
      (3*first.length+1)+((3*second.length+1)+((2*first.length+1)+(2*second.length+1))) := by omega
  rw [start, time, Machine.run_add, parse_first, Option.bind_some, List.append_nil,
    Machine.run_add, parse_second, Option.bind_some, List.append_nil, Machine.run_add]
  have firstRun := restore_first (input := suffix) (output := []) (ar := first.reverse)
    (br := second.reverse) (a := []) (b := []) (result := [])
  simp only [List.length_reverse, List.reverse_reverse, List.append_nil] at firstRun
  rw [firstRun, Option.bind_some]
  simpa only [List.length_reverse, List.reverse_reverse, List.append_nil] using
    restore_second suffix [] [] second.reverse first [] []

theorem arith_eq_addConfig (state : Control additionProgram)
    (input output ar br first second result : List Bool) :
    arithConfig state input output ar br first second result =
      addConfig state (arithConfig state input output ar br [] [] []).store first second result := by
  apply congrArg (Config.mk _)
  funext r
  fin_cases r <;> rfl

theorem carry_loop (input output ar br first second result : List Bool) :
    ∃ transitions ≤ 3*(first.length+second.length)+3,
      Machine.run (step additionProgram) transitions (arithConfig 18 input output ar br first second result) =
        some (arithConfig 34 input output ar br [] [] ((addBits false first second).reverse++result)) := by
  rw [arith_eq_addConfig]
  have proof := add_loop false first second result (arithConfig 18 input output ar br [] [] []).store
  have finish : arithConfig 34 input output ar br [] [] ((addBits false first second).reverse++result) =
      addConfig 34 (arithConfig 18 input output ar br [] [] []).store [] [] ((addBits false first second).reverse++result) := by
    rw [arith_eq_addConfig]
    rfl
  rw [finish]
  exact proof

end Counting.StackMachine.Arithmetic
