import Counting.StackRoutineLists

namespace Counting.StackMachine.Routine

/-- Repeated copies; concatenation order is explicit and executable. -/
def copies (count : Nat) (word : List Bool) : List Bool := (List.replicate count word).flatten

theorem copies_zero (word : List Bool) : copies 0 word = [] := rfl

theorem copies_succ (count : Nat) (word : List Bool) : copies (count+1) word = copies count word ++ word := by
  simp [copies,List.replicate_succ',List.flatten_append]

theorem copies_unary (count length : Nat) (bit : Bool) : copies count (List.replicate length bit) =
    List.replicate (count*length) bit := by
  induction count with
  | zero => simp [copies]
  | succ count ih =>
      rw [copies_succ,ih,← List.replicate_add]
      congr 1
      ring

abbrev repeatedCopy (extra : Nat) (source counter target temporary : Fin (extra+3)) : Routine (extra+1) :=
  forEach counter (ofProgram (ListPrograms.copyProgram extra source target temporary))

theorem repeatedCopy_executes (extra : Nat) (source counter target temporary : Fin (extra+3))
    (sc : source ≠ counter) (st : source ≠ target) (sw : source ≠ temporary)
    (ct : counter ≠ target) (cw : counter ≠ temporary) (tw : target ≠ temporary)
    (counterWord : List Bool) (store : Fin (extra+3) → List Bool)
    (contents : store counter = counterWord) (work : store temporary = []) :
    Executes (repeatedCopy extra source counter target temporary) store
      ((5*(store source).length+4)*counterWord.length+1)
      (Function.update (Function.update store counter []) target
        (copies counterWord.length (store source)++store target)) := by
  induction counterWord generalizing store with
  | nil =>
      have identity : Function.update (Function.update store counter []) target
          (copies 0 (store source)++store target) = store := by
        have cleared : Function.update store counter [] = store := by
          rw [← contents,Function.update_eq_self]
        simp only [copies_zero,List.nil_append,cleared,Function.update_eq_self]
      simp only [List.length_nil] at ⊢
      rw [identity]
      obtain ⟨ran,halted⟩ := repeat_empty counter
        (ofProgram (ListPrograms.copyProgram extra source target temporary)) store contents
      exact ⟨⟨1,store⟩,ran,halted,rfl⟩
  | cons bit rest ih =>
      let consumed := Function.update store counter rest
      let after := Function.update consumed target (store source++store target)
      have consumedSource : consumed source = store source := by simp [consumed,sc]
      have consumedTarget : consumed target = store target := by simp [consumed,Ne.symm ct]
      have consumedWork : consumed temporary = [] := by simp [consumed,Ne.symm cw,work]
      obtain ⟨middle,bodyRun,bodyHalt,bodyStore⟩ :=
        copy_executes extra source target temporary st sw tw consumed consumedWork
      have bodyResult : middle.store = after := by
        rw [bodyStore]
        funext register
        by_cases same : register = target
        · subst register
          simp [after,Function.update,consumedSource,consumedTarget]
        · simp [after,Function.update,same]
          intro equal
          exact False.elim (same equal)
      have nextContents : after counter = rest := by simp [after,consumed,ct]
      have nextWork : after temporary = [] := by simp [after,consumed,Ne.symm tw,Ne.symm cw,work]
      have nextSource : after source = store source := by simp [after,consumed,st,sc]
      have nextTarget : after target = store source++store target := by simp [after]
      obtain ⟨finish,tailRun,tailHalt,tailStore⟩ := ih after nextContents nextWork
      have firstRun := repeat_iteration counter
        (ofProgram (ListPrograms.copyProgram extra source target temporary)) store bit rest contents
        (5*(consumed source).length+2) middle bodyRun bodyHalt
      have time : (5*(store source).length+4)*(bit::rest).length+1 =
          (5*(consumed source).length+2+2)+((5*(after source).length+4)*rest.length+1) := by
        rw [consumedSource,nextSource,List.length_cons]
        ring
      refine ⟨finish,?_,tailHalt,?_⟩
      · rw [time,Machine.run_add,firstRun,Option.bind_some,bodyResult,tailRun]
      · rw [tailStore,nextSource,nextTarget,List.length_cons,copies_succ]
        funext register
        by_cases a : register = target
        · subst register
          simp [List.append_assoc]
        · by_cases b : register = counter
          · subst register
            simp [ct]
          · simp [after,consumed,a,b]

/-- Unary multiplication is a concrete loop of proved copy operations.
The multiplier is consumed; the multiplicand and other registers remain. -/
theorem unary_multiply_executes (extra : Nat) (source counter target temporary : Fin (extra+3))
    (sc : source ≠ counter) (st : source ≠ target) (sw : source ≠ temporary)
    (ct : counter ≠ target) (cw : counter ≠ temporary) (tw : target ≠ temporary)
    (multiplicand multiplier : Nat) (store : Fin (extra+3) → List Bool)
    (left : store source = List.replicate multiplicand true)
    (right : store counter = List.replicate multiplier true) (work : store temporary = []) :
    Executes (repeatedCopy extra source counter target temporary) store
      ((5*multiplicand+4)*multiplier+1)
      (Function.update (Function.update store counter []) target
        (List.replicate (multiplier*multiplicand) true++store target)) := by
  simpa only [left,List.length_replicate,copies_unary] using
    repeatedCopy_executes extra source counter target temporary sc st sw ct cw tw _ store right work

end Counting.StackMachine.Routine
