import Counting.StackRealizabilityReachStep

namespace Counting.StackMachine.RealizabilityCheck
open Routine
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

def reachIterations (width : Nat) (arcs : List Bool) : Nat → List Bool → List Bool
  | 0,seen=>seen
  | count+1,seen=>reachIterations width arcs count (RealizabilityVerifier.BitGraph.reachPass width arcs seen)

theorem reachIterations_iterate (width : Nat) (arcs : List Bool) (source : Fin width) (start count : Nat) :
    reachIterations width arcs count (RealizabilityVerifier.BitGraph.iterate width arcs source start)=
      RealizabilityVerifier.BitGraph.iterate width arcs source (start+count):=by
  induction count generalizing start with
  | zero=>simp [reachIterations]
  | succ count ih=>
    rw [reachIterations,←RealizabilityVerifier.BitGraph.iterate,ih]
    congr 1
    omega

def reachIterationStore (store : Store 15) (count : Nat) : Store 15:=
  Function.update (Function.update store 8 []) 1
    (reachIterations (store 2).length (store 0) count (store 1))

/-- The eighth register is a consumed explicit iteration counter. Every other
non-output register is preserved, including arbitrary graph data. -/
theorem reachIteration_executes (store : Store 15) (counter : List Bool) (counted : store 8=counter)
    (seenBound : Nat) (seenLength : (store 1).length ≤ seenBound) (widthBound : (store 2).length ≤ seenBound)
    (e3 : store 3=[]) (e4 : store 4=[]) (e5 : store 5=[]) (e6 : store 6=[]) (e7 : store 7=[])
    (e9 : store 9=[]) (e10 : store 10=[]) (e11 : store 11=[]) (e12 : store 12=[]) (e13 : store 13=[])
    (e14 : store 14=[]) (e15 : store 15=[]) (e16 : store 16=[]) :
    ∃ time ≤ counter.length*(11000*((store 0).length+seenBound+(store 2).length+1)^4+2)+1,
      Executes (forEach 8 reachStepRoutine) store time (reachIterationStore store counter.length):=by
  induction counter generalizing store with
  | nil=>
    obtain ⟨ran,halted⟩:=repeat_empty (8:Fin 17) reachStepRoutine store counted
    have final : reachIterationStore store 0=store:=by
      funext r
      by_cases r1 : r=1 <;> by_cases r8 : r=8 <;>
        simp [reachIterationStore,reachIterations,r1,r8,counted]
    exact ⟨1,by simp,⟨1,store⟩,ran,halted,final.symm⟩
  | cons bit counter ih=>
    let consumed:=Function.update store 8 counter
    obtain ⟨bodyTime,bodyBound,finishBody,bodyRun,bodyHalted,bodyStore⟩:=reachStep_executes consumed
      (by simp [consumed,e3]) (by simp [consumed,e4]) (by simp [consumed,e5])
      (by simp [consumed,e6]) (by simp [consumed,e7]) (by simp [consumed,e9])
      (by simp [consumed,e10]) (by simp [consumed,e11]) (by simp [consumed,e12]) (by simp [consumed,e13])
      (by simp [consumed,e14]) (by simp [consumed,e15]) (by simp [consumed,e16])
    let middle:=Function.update consumed 1
      (RealizabilityVerifier.BitGraph.reachPass (store 2).length (store 0) (store 1))
    have actual : Function.update consumed 1
        (RealizabilityVerifier.BitGraph.reachPass (consumed 2).length (consumed 0) (consumed 1))=middle:=by
      simp [middle,consumed]
    rw [actual] at bodyStore
    obtain ⟨tailTime,tailBound,finishTail,tailRun,tailHalted,tailStore⟩:=ih middle
      (by simp [middle,consumed])
      (by simpa [middle] using widthBound)
      (by simpa [middle,consumed] using widthBound)
      (by simp [middle,consumed,e3]) (by simp [middle,consumed,e4]) (by simp [middle,consumed,e5])
      (by simp [middle,consumed,e6]) (by simp [middle,consumed,e7]) (by simp [middle,consumed,e9])
      (by simp [middle,consumed,e10]) (by simp [middle,consumed,e11]) (by simp [middle,consumed,e12])
      (by simp [middle,consumed,e13]) (by simp [middle,consumed,e14]) (by simp [middle,consumed,e15])
      (by simp [middle,consumed,e16])
    have firstRun:=repeat_iteration (8:Fin 17) reachStepRoutine store bit counter counted bodyTime finishBody bodyRun bodyHalted
    have final : reachIterationStore middle counter.length=reachIterationStore store (bit::counter).length:=by
      funext r
      by_cases r1 : r=1 <;> by_cases r8 : r=8 <;>
        simp [reachIterationStore,reachIterations,middle,consumed,r1,r8]
    refine ⟨bodyTime+2+tailTime,?_,finishTail,?_,tailHalted,tailStore.trans final⟩
    · simp only [middle,consumed,Function.update_of_ne (by decide : (0:Fin 17)≠1),
        Function.update_of_ne (by decide : (0:Fin 17)≠8),Function.update_of_ne (by decide : (2:Fin 17)≠1),
        Function.update_of_ne (by decide : (2:Fin 17)≠8)] at tailBound
      simp only [consumed,Function.update_of_ne (by decide : (0:Fin 17)≠8),
        Function.update_of_ne (by decide : (1:Fin 17)≠8),Function.update_of_ne (by decide : (2:Fin 17)≠8)] at bodyBound
      let S:=(store 0).length+seenBound+(store 2).length+1
      have bodyLimit : bodyTime ≤ 11000*S^4:=by
        apply bodyBound.trans
        exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by dsimp only [S];omega) 4)
      change bodyTime+2+tailTime ≤ (bit::counter).length*(11000*S^4+2)+1
      change tailTime ≤ counter.length*(11000*S^4+2)+1 at tailBound
      simp only [List.length_cons,Nat.add_mul,Nat.one_mul]
      omega
    · rw [Machine.run_add,firstRun,Option.bind_some,bodyStore]
      exact tailRun

end Counting.StackMachine.RealizabilityCheck
