import Counting.ExternalCoefficientHeader

namespace Counting.External.CoefficientMachine
open StackMachine StackMachine.Routine
set_option backward.isDefEq.respectTransparency false

def finishCoefficients (extra : Nat) (w : Workspace extra) : Routine (extra+62) :=
  sequence (clear (w 1)) (ofProgram (ListPrograms.reverseProgram (extra+62) (w 36) (w 1)))

theorem finishCoefficients_executes (extra : Nat) (w : Workspace extra)
    (store : Fin (extra+64) → List Bool) (output : List Bool)
    (stream : store (w 36)=output.reverse) :
    Executes (finishCoefficients extra w) store ((store (w 1)).length+2*output.length+3)
      (Function.update (Function.update store (w 36) []) (w 1) output) := by
  have clearing:=clear_executes (w 1) store
  let cleared:=Function.update store (w 1) []
  have reversing:=reverse_executes (extra+62) (w 36) (w 1)
    (by simp [w.injective.eq_iff]) cleared
  have streamAt : cleared (w 36)=output.reverse := by simpa [cleared,w.injective.eq_iff] using stream
  rw [streamAt,List.length_reverse] at reversing
  have final : Function.update (Function.update cleared (w 36) []) (w 1)
      (output.reverse.reverse++cleared (w 1))=
      Function.update (Function.update store (w 36) []) (w 1) output := by
    funext r
    by_cases e1 : r=w 1
    · subst r;simp [cleared]
    · simp [cleared,Function.update_apply,e1]
  rw [final] at reversing
  have cost : (store (w 1)).length+1+1+(2*output.length+1)=
      (store (w 1)).length+2*output.length+3 := by omega
  rw [←cost]
  exact clearing.sequence reversing

end Counting.External.CoefficientMachine
