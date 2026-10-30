import Counting.StackEncodingRoutineInterfaces

namespace Counting.StackMachine.EncodingPrograms
set_option backward.isDefEq.respectTransparency false

/-- Exact whole-store interface for the existing unframer on a framed
payload. The caller supplies canonical framing, not a free decoded value. -/
theorem unframe_canonical_executes (extra : Nat) (source target scratch : Fin (extra+3))
    (st : source≠target) (ss : source≠scratch) (ts : target≠scratch)
    (store : Fin (extra+3) → List Bool) (payload suffix : List Bool)
    (input : store source=Encoding.frame payload++suffix) (empty : store scratch=[]) :
    Routine.Executes (Routine.ofProgram (unframeProgram extra source target scratch)) store
      (5*payload.length+2)
      (Function.update (Function.update store source suffix) target (payload++store target)) := by
  have start : unframeConfig extra source target scratch 0 store (Encoding.frame payload++suffix) (store target) []=
      (⟨0,store⟩ : Config (unframeProgram extra source target scratch)) := by
    apply congrArg (Config.mk _)
    change (fun r : Fin (extra+3) => _) = store
    funext r
    by_cases a : r=source
    · subst r; simp only [ite_true,input]
    · by_cases b : r=target
      · subst r; simp only [a,if_false,ite_true]
      · by_cases c : r=scratch
        · subst r; simp only [a,b,if_false,ite_true,empty]
        · simp only [a,b,c,if_false]
  have ran := unframe_frames extra source target scratch st ss ts store payload suffix (store target)
  rw [start] at ran
  refine ⟨unframeConfig extra source target scratch 7 store suffix (payload++store target) [],ran,
    (unframe_halted _ _ _ _ _ _ _ _).1,?_⟩
  dsimp only [unframeConfig]
  funext r
  by_cases a : r=source
  · subst r; simp only [ite_true,Function.update_of_ne st,Function.update_self]
  · by_cases b : r=target
    · subst r; simp only [a,if_false,ite_true,Function.update_self]
    · by_cases c : r=scratch
      · subst r; simp only [a,b,if_false,ite_true,Function.update_of_ne a,Function.update_of_ne b,empty]
      · simp only [a,b,c,if_false,Function.update_of_ne a,Function.update_of_ne b]

end Counting.StackMachine.EncodingPrograms
