import Counting.StackRoutineBasic

namespace Counting.StackMachine.Routine

/-- Three consumed unary cells cause one emitted unary cell. Incomplete
last groups are consumed too; the exact theorem below uses multiples of3. -/
def quotientThree (source target : Fin (extra+2)) : Routine extra :=
  ⟨4,fun control=>match control.val with
    | 0=>.pop source 4 1 1
    | 1=>.pop source 4 2 2
    | 2=>.pop source 4 3 3
    | 3=>.push target true 0
    | _=>.halt⟩

set_option backward.isDefEq.respectTransparency false in
theorem quotientThree_executes (source target : Fin (extra+2)) (different : source≠target)
    (q : Nat) (store : Store extra) (input : store source=List.replicate (3*q) true) :
    Executes (quotientThree source target) store (4*q+1)
      (Function.update (Function.update store source []) target (List.replicate q true++store target)) := by
  induction q generalizing store with
  | zero =>
    have empty : store source=[] := by simpa using input
    have reset : Function.update store source []=store := by rw [←empty,Function.update_eq_self]
    refine ⟨⟨4,store⟩,?_,rfl,?_⟩
    · simp [Machine.run,step,quotientThree,empty]
    · simp [reset]
  | succ q ih =>
    let next := Function.update (Function.update store source (List.replicate (3*q) true)) target (true::store target)
    have nextInput : next source=List.replicate (3*q) true := by simp [next,different]
    obtain ⟨finish,ran,halted,result⟩ := ih next nextInput
    have first : Machine.run (step (quotientThree source target).program) 4 ⟨0,store⟩=some ⟨0,next⟩ := by
      have three : 3*(q+1)=3*q+1+1+1 := by omega
      simp [Machine.run,step,quotientThree,input,three,List.replicate_succ,Function.update_idem,next,Ne.symm different]
    refine ⟨finish,?_,halted,?_⟩
    · rw [show 4*(q+1)+1=4+(4*q+1) by omega,Machine.run_add,first,Option.bind_some]
      exact ran
    · rw [result]
      have unary (n : Nat) : List.replicate n true++true::store target=true::(List.replicate n true++store target) := by
        induction n with
        | zero => rfl
        | succ n ih => simpa only [List.replicate_succ,List.cons_append] using congrArg (List.cons true) ih
      funext r
      by_cases a : r=source
      · subst r;simp [next,different]
      · by_cases b : r=target
        · subst r;simp [next,List.replicate_succ,unary]
        · simp [next,a,b]

end Counting.StackMachine.Routine
