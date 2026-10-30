import Counting.StackUnaryMultiply
import Counting.HardnessNetworkMachineRow

namespace Counting.HardnessNetworkMachine
open StackMachine StackMachine.Routine
set_option backward.isDefEq.respectTransparency false

abbrev RepeatWorkspace (extra : Nat) := Fin 5 ↪ Fin (extra+5)

def emitRepeatedCode (extra : Nat) (w : RepeatWorkspace extra) : Routine (extra+3) :=
  sequence (ofProgram (ListPrograms.reverseProgram (extra+3) (w 0) (w 3)))
    (sequence (repeatedCopy (extra+2) (w 3) (w 1) (w 2) (w 4)) (clear (w 3)))

def repeatedCodeResult (w : RepeatWorkspace extra) (store : Fin (extra+5) → List Bool) :=
  Function.update (Function.update (Function.update store (w 0) []) (w 1) []) (w 2)
    (copies (store (w 1)).length (store (w 0)).reverse++store (w 2))

/-- Copy a framed binary multiplicity once per explicitly represented agent.
The multiplicity itself is never expanded into a unary counter. -/
theorem emitRepeatedCode_executes (extra : Nat) (w : RepeatWorkspace extra)
    (store : Fin (extra+5) → List Bool) (buffer : store (w 3)=[]) (scratch : store (w 4)=[]) :
    Executes (emitRepeatedCode extra w) store
      (3*(store (w 0)).length+(5*(store (w 0)).length+4)*(store (w 1)).length+5)
      (repeatedCodeResult w store) := by
  have reversing:=reverse_executes (extra+3) (w 0) (w 3) (by simp [w.injective.eq_iff]) store
  rw [buffer,List.append_nil] at reversing
  let reversed:=Function.update (Function.update store (w 0) []) (w 3) (store (w 0)).reverse
  have repeating:=repeatedCopy_executes (extra+2) (w 3) (w 1) (w 2) (w 4)
    (by simp [w.injective.eq_iff]) (by simp [w.injective.eq_iff]) (by simp [w.injective.eq_iff])
    (by simp [w.injective.eq_iff]) (by simp [w.injective.eq_iff]) (by simp [w.injective.eq_iff])
    (store (w 1)) reversed (by simp [reversed,w.injective.eq_iff])
    (by simp [reversed,w.injective.eq_iff,scratch])
  let repeated:=Function.update (Function.update reversed (w 1) []) (w 2)
    (copies (store (w 1)).length (store (w 0)).reverse++store (w 2))
  have repeatingAs : Executes (repeatedCopy (extra+2) (w 3) (w 1) (w 2) (w 4)) reversed
      ((5*(store (w 0)).length+4)*(store (w 1)).length+1) repeated := by
    simpa [reversed,repeated,w.injective.eq_iff] using repeating
  have cleaning:=clear_executes (w 3) repeated
  have codeAt : repeated (w 3)=(store (w 0)).reverse := by simp [repeated,reversed,w.injective.eq_iff]
  rw [codeAt,List.length_reverse] at cleaning
  have final : Function.update repeated (w 3) []=repeatedCodeResult w store := by
    funext r
    by_cases e3 : r=w 3
    · subst r;simp [repeatedCodeResult,w.injective.eq_iff,buffer]
    · simp [repeated,reversed,repeatedCodeResult,Function.update_apply,e3]
  rw [final] at cleaning
  have combined:=reversing.sequence (repeatingAs.sequence cleaning)
  have cost : 2*(store (w 0)).length+1+1+
      ((5*(store (w 0)).length+4)*(store (w 1)).length+1+1+((store (w 0)).length+1))=
      3*(store (w 0)).length+(5*(store (w 0)).length+4)*(store (w 1)).length+5 := by omega
  rw [cost] at combined
  exact combined

theorem repeated_natural_code (value count : Nat) :
    copies count (Encoding.natural.encode value).reverse=
      (Encoding.sequence Encoding.natural (List.replicate count value)).reverse := by
  induction count with
  | zero=>rfl
  | succ count ih=>
    rw [copies_succ,ih,List.replicate_succ,Encoding.sequence,List.reverse_append]

end Counting.HardnessNetworkMachine
