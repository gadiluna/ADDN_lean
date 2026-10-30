import Counting.StackRoutineBasic

namespace Counting.StackMachine.Routine

/-- A constant finite-state scan; the counter is consumed, the result is
pushed onto the output, and all other registers are preserved. -/
def divisibleThree (counter output : Fin (extra+2)) : Routine extra :=
  ⟨5,fun control=>match control.val with
    | 0=>.pop counter 3 1 1
    | 1=>.pop counter 4 2 2
    | 2=>.pop counter 4 0 0
    | 3=>.push output true 5
    | 4=>.push output false 5
    | _=>.halt⟩

set_option backward.isDefEq.respectTransparency false in
theorem divisibleThree_executes (counter output : Fin (extra+2)) (different : counter≠output)
    (n : Nat) (store : Store extra) (count : store counter=List.replicate n true) :
    Executes (divisibleThree counter output) store (n+2)
      (Function.update (Function.update store counter []) output
        (decide (n%3=0)::store output)) := by
  induction n using Nat.strong_induction_on generalizing store with
  | h n ih =>
    cases n with
    | zero =>
      have empty : store counter=[]:=count
      have unchanged : Function.update store counter []=store := by rw [←empty,Function.update_eq_self]
      refine ⟨⟨5,_⟩,?_,?_,rfl⟩
      · simp [Machine.run,step,divisibleThree,empty,unchanged]
        funext r
        cases instDecidableEqFin (extra+2) r output <;> simp_all
      · simp [step,divisibleThree]
    | succ n =>
      cases n with
      | zero =>
        refine ⟨⟨5,_⟩,?_,?_,rfl⟩
        · simp [Machine.run,step,divisibleThree,count,Ne.symm different]
          funext r
          cases instDecidableEqFin (extra+2) r output <;> simp_all [Function.update_apply]
        · simp [step,divisibleThree]
      | succ n =>
        cases n with
        | zero =>
          refine ⟨⟨5,_⟩,?_,?_,rfl⟩
          · simp [Machine.run,step,divisibleThree,count,Function.update_idem,Ne.symm different]
            funext r
            cases instDecidableEqFin (extra+2) r output <;> simp_all [Function.update_apply]
          · simp [step,divisibleThree]
        | succ n =>
          let smaller:=Function.update store counter (List.replicate n true)
          obtain ⟨finish,ran,halted,result⟩:=ih n (by omega) smaller (by simp [smaller])
          have first : Machine.run (step (divisibleThree counter output).program) 3 ⟨0,store⟩=
              some ⟨0,smaller⟩ := by
            simp [Machine.run,step,divisibleThree,count,List.replicate_succ,Function.update_idem,smaller]
          refine ⟨finish,?_,halted,?_⟩
          · rw [show n+1+1+1+2=3+(n+2) by omega,Machine.run_add,first,Option.bind_some]
            exact ran
          · simpa [smaller,Function.update_idem,Ne.symm different,
              show (n+1+1+1)%3=n%3 by omega] using result

end Counting.StackMachine.Routine
