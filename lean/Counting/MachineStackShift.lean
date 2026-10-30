import Counting.MachineModel

namespace Counting.Machine.StackShift

/-- Concrete symbol numbering, independent of any unbounded data. -/
def symbolCode : Symbol → Fin 5
  | .blank => 0 | .zero => 1 | .one => 2 | .separator => 3 | .mark => 4

def codeSymbol : Nat → Symbol
  | 0 => .blank | 1 => .zero | 2 => .one | 3 => .separator | _ => .mark

def carryState (symbol : Symbol) : Fin 10 := ⟨(symbolCode symbol).val, by have := (symbolCode symbol).isLt; omega⟩
def moveState (symbol : Symbol) : Fin 10 := ⟨(symbolCode symbol).val+5, by have := (symbolCode symbol).isLt; omega⟩

/-- Carry one finite alphabet symbol to the right. The first blank ends
insertion after the carried symbol is written and the head moves once. -/
def insertionProgram : Program where
  states := 9
  code state symbol :=
    if state.val < 5 then
      if state.val = 0 ∧ symbol = .blank then none
      else some (moveState symbol, .write (codeSymbol state.val))
    else some (⟨state.val-5, by have := state.isLt; omega⟩, .move .right)
  accept state := state == 0

def insertionStart (carry : Symbol) (left suffix : List Symbol) : Config insertionProgram :=
  ⟨carryState carry, ⟨left, suffix.headD .blank, suffix.tail⟩⟩

def insertionEnd (carry : Symbol) (left suffix : List Symbol) : Config insertionProgram :=
  ⟨0, ⟨suffix.reverse ++ carry::left, .blank, []⟩⟩

/-- Exact physical insertion cost, starting in a finite carry state and
ending immediately to the right of the shifted suffix. The arbitrary left
part is preserved; no movement back to a caller's marker is charged here. -/
theorem insertion_run (carry : Symbol) (nonblank : carry ≠ .blank) (left suffix : List Symbol)
    (symbols : ∀ symbol ∈ suffix, symbol ≠ .blank) :
    run (step insertionProgram) (2*(suffix.length+1)) (insertionStart carry left suffix) =
      some (insertionEnd carry left suffix) := by
  induction suffix generalizing carry left with
  | nil => cases carry <;> first | contradiction | rfl
  | cons symbol suffix ih =>
      have present : symbol ≠ .blank := symbols symbol List.mem_cons_self
      have rest : ∀ value ∈ suffix, value ≠ .blank := fun value member => symbols value (List.mem_cons_of_mem symbol member)
      have time : 2*((symbol::suffix).length+1) = 2+2*(suffix.length+1) := by simp only [List.length_cons]; omega
      rw [time, run_add]
      have first : run (step insertionProgram) 2 (insertionStart carry left (symbol::suffix)) =
          some (insertionStart symbol (carry::left) suffix) := by
        cases carry <;> cases symbol <;> first | contradiction | rfl
      rw [first, Option.bind_some, ih symbol present (carry::left) rest]
      simp only [insertionEnd, List.reverse_cons, List.append_assoc, List.singleton_append]

theorem insertion_halted (carry : Symbol) (left suffix : List Symbol) :
    step insertionProgram (insertionEnd carry left suffix) = none := rfl

/-- Inserting a bit into the stack tape shifts bits and separators without
expanding their encodings or assuming a unit-cost bulk operation. -/
theorem insert_bit_run (bit : Bool) (left suffix : List Symbol)
    (symbols : ∀ symbol ∈ suffix, symbol ≠ .blank) :
    run (step insertionProgram) (2*(suffix.length+1)) (insertionStart (bitSymbol bit) left suffix) =
      some (insertionEnd (bitSymbol bit) left suffix) :=
  insertion_run (bitSymbol bit) (bitSymbol_ne_blank bit) left suffix symbols

end Counting.Machine.StackShift
