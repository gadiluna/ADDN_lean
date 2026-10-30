import Counting.StackLoop
import Counting.StackRoutineBasic

namespace Counting.StackMachine.Routine
set_option backward.isDefEq.respectTransparency false

abbrev repeatBit (counter target : Fin (extra+2)) (bit : Bool) : Routine extra :=
  forEach counter (pushBit target bit)

/-- Each consumed counter cell pays a pop, push, and jump. The counter's
bit values are irrelevant; all registers outside counter/target survive. -/
theorem repeatBit_executes (counter target : Fin (extra+2)) (bit : Bool)
    (different : counter≠target) (store : Store extra) :
    Executes (repeatBit counter target bit) store (3*(store counter).length+1)
      (Function.update (Function.update store counter []) target
        (List.replicate (store counter).length bit++store target)) := by
  generalize content : store counter=bits
  induction bits generalizing store with
  | nil =>
    obtain ⟨ran,halted⟩ := repeat_empty counter (pushBit target bit) store content
    refine ⟨⟨1,store⟩,ran,halted,?_⟩
    have reset : Function.update store counter []=store := by rw [←content,Function.update_eq_self]
    simp [reset]
  | cons head tail ih =>
    let consumed := Function.update store counter tail
    let next := Function.update consumed target (bit::store target)
    have nextContent : next counter=tail := by simp [next,consumed,different]
    have push := pushBit_executes target bit consumed
    have pushAs : Function.update consumed target (bit::consumed target)=next := by
      simp [next,consumed,Ne.symm different]
    rw [pushAs] at push
    obtain ⟨bodyLast,bodyRan,bodyHalted,bodyStored⟩ := push
    have first := repeat_iteration counter (pushBit target bit) store head tail content 1 bodyLast bodyRan bodyHalted
    change Machine.run (step (repeatBit counter target bit).program) 3 ⟨0,store⟩=some ⟨0,bodyLast.store⟩ at first
    rw [bodyStored] at first
    obtain ⟨last,ran,halted,stored⟩ := ih next nextContent
    refine ⟨last,?_,halted,?_⟩
    · rw [List.length_cons,show 3*(tail.length+1)+1=3+(3*tail.length+1) by omega,
        Machine.run_add,first,Option.bind_some]
      exact ran
    · rw [stored]
      have commute (n : Nat) : List.replicate n bit++bit::store target=
          bit::(List.replicate n bit++store target) := by
        induction n with
        | zero => rfl
        | succ n ih => simpa only [List.replicate_succ,List.cons_append] using congrArg (List.cons bit) ih
      funext r
      by_cases a : r=counter
      · subst r;simp [next,consumed,different]
      · by_cases b : r=target
        · subst r;simp [next,List.replicate_succ,commute]
        · simp [next,consumed,a,b]

end Counting.StackMachine.Routine
