import Counting.ExternalMatchingRepeated
import Counting.StackRoutineBasic

namespace Counting.External.MatchingMachine
open StackMachine StackMachine.Routine
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 700000

def pairRows (first second third : Nat) : List (List Nat) :=
  [[first,first,first],[first,second,third]]

def emitPair (extra : Nat) (w : EdgeWorkspace extra) : Routine (extra+10) :=
  sequence (emitRepeated extra w) (emitEdge extra w)

theorem emitPair_executes (extra : Nat) (w : EdgeWorkspace extra) (store : Fin (extra+12) → List Bool)
    (empty : ∀ i∈([3,4,5,7,8,9,10,11] : List (Fin 12)),store (w i)=[]) :
    ∃ time ≤ 401*((store (w 0)).length+(store (w 1)).length+(store (w 2)).length+1)^2,
      Executes (emitPair extra w) store time (Function.update store (w 6)
        ((Encoding.sequence (Encoding.list Encoding.natural)
          (pairRows (store (w 0)).length (store (w 1)).length (store (w 2)).length)).reverse++store (w 6))) := by
  obtain ⟨repeatedTime,repeatedBound,repeatedRun⟩ := emitRepeated_executes extra w store
    (fun i mem=>empty i (by simp only [List.mem_cons,List.not_mem_nil] at *;tauto))
  let first := (Encoding.list Encoding.natural).encode
    [(store (w 0)).length,(store (w 0)).length,(store (w 0)).length]
  let middle := Function.update store (w 6) (first.reverse++store (w 6))
  have middleEmpty (i : Fin 12) (member : i∈([3,4,5,7,8,9,10,11] : List (Fin 12))) : middle (w i)=[] := by
    have different : i≠6 := by intro same;subst i;simp at member
    simpa [middle,w.injective.eq_iff,different] using empty i member
  obtain ⟨edgeTime,edgeBound,edgeRun⟩ := emitEdge_executes extra w middle middleEmpty
  have combined := repeatedRun.sequence edgeRun
  refine ⟨repeatedTime+1+edgeTime,?_,?_⟩
  · let S := (store (w 0)).length+(store (w 1)).length+(store (w 2)).length+1
    have repeatedLimit : repeatedTime ≤ 100*S^2 := repeatedBound.trans
      (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by dsimp [S];omega) 2))
    have edgeLimit : edgeTime ≤ 300*S^2 := by simpa [middle,w.injective.eq_iff,S] using edgeBound
    have positive : 1 ≤ S^2 := Nat.one_le_pow _ _ (by dsimp [S];omega)
    change _ ≤ 401*S^2
    omega
  · simpa [emitPair,middle,first,w.injective.eq_iff,Function.update_idem,pairRows,Encoding.sequence,
      List.reverse_append,List.append_assoc] using combined

def emitVariableStep (extra : Nat) (w : EdgeWorkspace extra) : Routine (extra+10) :=
  sequence (emitPair extra w)
    (sequence (pushBit (w 0) true) (sequence (pushBit (w 1) true) (pushBit (w 2) true)))

def variableStepResult (extra : Nat) (w : EdgeWorkspace extra) (store : Fin (extra+12) → List Bool) :=
  Function.update (Function.update (Function.update (Function.update store (w 6)
    ((Encoding.sequence (Encoding.list Encoding.natural)
      (pairRows (store (w 0)).length (store (w 1)).length (store (w 2)).length)).reverse++store (w 6)))
    (w 0) (true::store (w 0))) (w 1) (true::store (w 1))) (w 2) (true::store (w 2))

theorem emitVariableStep_executes (extra : Nat) (w : EdgeWorkspace extra) (store : Fin (extra+12) → List Bool)
    (empty : ∀ i∈([3,4,5,7,8,9,10,11] : List (Fin 12)),store (w i)=[]) :
    ∃ time ≤ 410*((store (w 0)).length+(store (w 1)).length+(store (w 2)).length+1)^2,
      Executes (emitVariableStep extra w) store time (variableStepResult extra w store) := by
  obtain ⟨pairTime,pairBound,pairRun⟩ := emitPair_executes extra w store empty
  let coded := Function.update store (w 6)
    ((Encoding.sequence (Encoding.list Encoding.natural)
      (pairRows (store (w 0)).length (store (w 1)).length (store (w 2)).length)).reverse++store (w 6))
  let incremented0 := Function.update coded (w 0) (true::coded (w 0))
  let incremented1 := Function.update incremented0 (w 1) (true::incremented0 (w 1))
  have a := pushBit_executes (w 0) true coded
  have b := pushBit_executes (w 1) true incremented0
  have c := pushBit_executes (w 2) true incremented1
  have combined := pairRun.sequence (a.sequence (b.sequence c))
  refine ⟨pairTime+6,?_,?_⟩
  · have positive : 1 ≤ ((store (w 0)).length+(store (w 1)).length+(store (w 2)).length+1)^2 :=
      Nat.one_le_pow _ _ (by omega)
    omega
  · simpa [emitVariableStep,variableStepResult,coded,incremented0,incremented1,w.injective.eq_iff] using combined

end Counting.External.MatchingMachine
