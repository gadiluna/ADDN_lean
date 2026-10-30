import Counting.AuditPrefixSpec

namespace Counting.StackMachine.AuditPrefix

def lastMatch (predicate : Nat→Bool) (initial : Option Nat) (indices : List Nat) : Option Nat :=
  indices.foldl (fun found index=>if predicate index then some index else found) initial

/-- The ascending scan overwrites its saved match, so its final answer is
exactly the first match in the reverse order used by auditPrefix?. -/
theorem lastMatch_eq_reverse_find (predicate : Nat→Bool) (initial : Option Nat) (indices : List Nat) :
    lastMatch predicate initial indices=(indices.reverse.find? predicate).or initial := by
  induction indices generalizing initial with
  | nil=>rfl
  | cons index indices ih=>
    simp only [lastMatch,List.foldl_cons] at ih ⊢
    rw [ih]
    simp only [List.reverse_cons,List.find?_append,List.find?_singleton]
    cases indices.reverse.find? predicate <;> cases predicate index <;> rfl

theorem lastMatch_append (predicate : Nat→Bool) (initial : Option Nat) (first second : List Nat) :
    lastMatch predicate initial (first++second)=lastMatch predicate (lastMatch predicate initial first) second := by
  simp only [lastMatch,List.foldl_append]

theorem lastMatch_range_succ (predicate : Nat→Bool) (initial : Option Nat) (count : Nat) :
    lastMatch predicate initial (List.range (count+1))=
      if predicate count then some count else lastMatch predicate initial (List.range count) := by
  rw [List.range_succ,lastMatch_append]
  rfl

theorem lastMatch_range'_succ (predicate : Nat→Bool) (initial : Option Nat) (start count : Nat) :
    lastMatch predicate initial (List.range' start (count+1))=
      if predicate (start+count) then some (start+count) else lastMatch predicate initial (List.range' start count) := by
  rw [List.range'_concat,lastMatch_append]
  simp only [lastMatch,List.foldl_cons,List.foldl_nil,Nat.one_mul]

theorem flat_zero (vista : Executable.Vista) : Executable.flat vista 0=false := by
  simp [Executable.flat]

/-- The physical round loop visits levels 1,...,last. Omitting level zero
preserves the exact executable answer because level zero is never flat. -/
theorem lastFlat_eq (vista : Executable.Vista) (last : Nat) :
    lastMatch (Executable.flat vista) none (List.range' 1 last)=
      ((List.range (last+1)).reverse).find? (Executable.flat vista) := by
  have zero:=flat_zero vista
  have full:=lastMatch_eq_reverse_find (Executable.flat vista) none (List.range (last+1))
  simp only [Option.or_none] at full
  rw [List.range_eq_range',List.range'_succ] at full
  rw [List.range_eq_range',List.range'_succ]
  simpa only [lastMatch,List.foldl_cons,zero,Bool.false_eq_true,if_false,Nat.zero_add] using full

end Counting.StackMachine.AuditPrefix
