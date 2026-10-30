import Counting.MachineStackShift

namespace Counting.Machine.StackShift

def deletionCarryState (symbol : Symbol) : Fin 10 :=
  ⟨(symbolCode symbol).val+2, by have := (symbolCode symbol).isLt; omega⟩

/-- Move each suffix symbol into the preceding cell. The erased final
cell and the final move are explicit machine transitions. -/
def deletionProgram : Program where
  states := 9
  code state symbol := match state.val with
    | 0 => some (1, .move .right)
    | 1 => some (deletionCarryState symbol, .move .left)
    | 2 => some (8, .write .blank)
    | 3 => some (7, .write .zero)
    | 4 => some (7, .write .one)
    | 5 => some (7, .write .separator)
    | 6 => some (7, .write .mark)
    | 7 => some (0, .move .right)
    | 8 => some (9, .move .right)
    | _ => none
  accept state := state == 9

def deletionStart (removed : Symbol) (left suffix : List Symbol) : Config deletionProgram :=
  ⟨0, ⟨left, removed, suffix⟩⟩

def deletionEnd (left suffix : List Symbol) : Config deletionProgram :=
  ⟨9, ⟨.blank :: (suffix.reverse ++ left), .blank, []⟩⟩

/-- Exact deletion run. `suffix` may contain stack separators and markers
but no embedded blanks. The arbitrary prefix is unchanged. The head ends
one cell beyond the newly erased final cell, whose blank is represented
explicitly on the left; a caller's rewind is a separate charged phase. -/
theorem deletion_run (removed : Symbol) (left suffix : List Symbol)
    (symbols : ∀ symbol ∈ suffix, symbol ≠ .blank) :
    run (step deletionProgram) (4*(suffix.length+1)) (deletionStart removed left suffix) =
      some (deletionEnd left suffix) := by
  induction suffix generalizing removed left with
  | nil => rfl
  | cons symbol suffix ih =>
      have present : symbol ≠ .blank := symbols symbol List.mem_cons_self
      have rest : ∀ value ∈ suffix, value ≠ .blank := fun value member => symbols value (List.mem_cons_of_mem symbol member)
      have time : 4*((symbol::suffix).length+1) = 4+4*(suffix.length+1) := by simp only [List.length_cons]; omega
      rw [time, run_add]
      have first : run (step deletionProgram) 4 (deletionStart removed left (symbol::suffix)) =
          some (deletionStart symbol (symbol::left) suffix) := by
        cases symbol <;> first | contradiction | rfl
      rw [first, Option.bind_some, ih symbol (symbol::left) rest]
      simp only [deletionEnd, List.reverse_cons, List.append_assoc, List.singleton_append]

theorem deletion_halted (left suffix : List Symbol) :
    step deletionProgram (deletionEnd left suffix) = none := rfl

end Counting.Machine.StackShift
