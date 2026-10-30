import Counting.StackRealizabilityReachPass

namespace Counting.StackMachine.RealizabilityCheck
open Routine
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-- Replace the old `seen` vector by the synchronous next vector. -/
def reachStepRoutine : Routine 15:=sequence reachPassRoutine
  (sequence (clear 1) (sequence (ofProgram (ListPrograms.reverseProgram 15 3 4))
    (ofProgram (ListPrograms.reverseProgram 15 4 1))))

theorem reachStep_executes (store : Store 15)
    (e3 : store 3=[]) (e4 : store 4=[]) (e5 : store 5=[]) (e6 : store 6=[]) (e7 : store 7=[])
    (e9 : store 9=[]) (e10 : store 10=[]) (e11 : store 11=[]) (e12 : store 12=[]) (e13 : store 13=[])
    (e14 : store 14=[]) (e15 : store 15=[]) (e16 : store 16=[]) :
    ∃ time ≤ 11000*((store 0).length+(store 1).length+(store 2).length+1)^4,
      Executes reachStepRoutine store time (Function.update store 1
        (RealizabilityVerifier.BitGraph.reachPass (store 2).length (store 0) (store 1))):=by
  obtain ⟨time,bound,passing⟩:=reachPass_executes store e3 e4 e5 e6 e7 e9 e10 e11 e12 e13 e14 e15 e16
  let bits:=RealizabilityVerifier.BitGraph.reachPass (store 2).length (store 0) (store 1)
  let passed:=Function.update store 3 bits
  have clearing:=clear_executes (1:Fin 17) passed
  have oldAt : passed 1=store 1:=by simp [passed]
  rw [oldAt] at clearing
  let cleared:=Function.update passed 1 []
  have first:=reverse_executes 15 3 4 (by decide) cleared
  have bitsAt : cleared 3=bits:=by simp [cleared,passed]
  have emptyAt : cleared 4=[]:=by simp [cleared,passed,e4]
  rw [bitsAt,emptyAt,List.append_nil] at first
  let reversed:=Function.update (Function.update cleared 3 []) 4 bits.reverse
  have second:=reverse_executes 15 4 1 (by decide) reversed
  have reverseAt : reversed 4=bits.reverse:=by simp [reversed]
  have seenAt : reversed 1=[]:=by simp [reversed,cleared]
  rw [reverseAt,seenAt,List.append_nil,List.reverse_reverse,List.length_reverse] at second
  have final : Function.update (Function.update reversed 4 []) 1 bits=Function.update store 1 bits:=by
    funext r
    fin_cases r <;> simp [reversed,cleared,passed,e3,e4]
  rw [final] at second
  have length : bits.length=(store 2).length:=RealizabilityVerifier.BitGraph.reachPass_length ..
  rw [length] at first second
  let S:=(store 0).length+(store 1).length+(store 2).length+1
  have linear : S ≤ S^4:=Nat.le_self_pow (by decide) _
  have one : 1 ≤ S^4:=Nat.one_le_pow _ _ (by dsimp only [S];omega)
  exact ⟨_,by change _ ≤ 11000*S^4;dsimp only [S] at linear one ⊢;omega,
    passing.sequence (clearing.sequence (first.sequence second))⟩

end Counting.StackMachine.RealizabilityCheck
