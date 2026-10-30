import Counting.StackAuditPropagationDownItem

namespace Counting.StackMachine.AuditPropagation
open Routine
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000

abbrev downLoop : Routine 38 := forEach 39 downItem

def downLoopBudget (vista : Executable.Vista) (tableLength : Nat) : Nat → Array Nat → Nat
  | 0,_ => 1
  | rounds+1,weights => downItemBudget vista rounds tableLength weights+2+
      downLoopBudget vista tableLength rounds (Executable.propagateLevel vista weights rounds)

def downLoopStore (store : Store 38) (vista : Executable.Vista) (rounds : Nat) (weights : Array Nat) : Store 38 :=
  Function.update (Function.update (Function.update store 39 []) 22 []) 35
    ((Encoding.array Encoding.natural).encode (Executable.propagateDown vista rounds weights))

/-- The binary level register follows the descending counter exactly. Each
level invokes the physical node loop; the result is the executable's exact
`propagateDown`, including zero levels and empty DAGs. -/
theorem downLoop_executes (store : Store 38) (accepted : Bool) (tail : List Bool)
    (status : store 1=accepted::tail)
    (work : ∀ i : Fin 40,i.val<17 → i≠1 → store i=[])
    (e18 : store 18=[]) (e19 : store 19=[]) (e20 : store 20=[]) (e21 : store 21=[])
    (e23 : store 23=[]) (e24 : store 24=[]) (e25 : store 25=[])
    (e26 : store 26=[]) (e30 : store 30=[]) (e31 : store 31=[]) (e32 : store 32=[])
    (e33 : store 33=[]) (e37 : store 37=[]) (e38 : store 38=[])
    (vista : Executable.Vista) (weights : Array Nat) (length : weights.size=vista.nodes.size)
    (nodeInput : store 34=Encoding.vista.encode vista)
    (table : store 17=Encoding.sequence Encoding.node vista.nodes.toList++Encoding.natural.encode vista.bottom)
    (weightInput : store 35=(Encoding.array Encoding.natural).encode weights)
    (nodeCount : store 36=List.replicate vista.nodes.size true)
    (rounds : Nat) (level : store 22=rounds.bits)
    (bits : List Bool) (counter : store 39=bits) (countEq : bits.length=rounds) :
    ∃ time ≤ downLoopBudget vista (store 17).length rounds weights,
      Executes downLoop store time (downLoopStore store vista rounds weights) := by
  induction rounds generalizing store weights bits with
  | zero =>
    have empty : store 39=[] := counter.trans (List.length_eq_zero_iff.mp countEq)
    have levelEmpty : store 22=[] := level
    obtain ⟨ran,halted⟩ := repeat_empty (39:Fin 40) downItem store empty
    have finish : downLoopStore store vista 0 weights=store := by
      change Function.update (Function.update (Function.update store 39 []) 22 []) 35
        ((Encoding.array Encoding.natural).encode weights)=store
      funext i
      by_cases i22 : i=22 <;> by_cases i35 : i=35 <;> by_cases i39 : i=39 <;>
        simp [i22,i35,i39,empty,levelEmpty,weightInput]
    exact ⟨1,by rfl,⟨1,store⟩,ran,halted,finish.symm⟩
  | succ rounds ih =>
    cases bits with
    | nil => simp at countEq
    | cons bit bits =>
      let consumed := Function.update store 39 bits
      have consumedWork (i : Fin 40) (small : i.val<17) (different : i≠1) : consumed i=[] := by
        have n39 : i≠39 := by intro same;subst i;norm_num at small
        simp [consumed,n39,work i small different]
      obtain ⟨bodyTime,bodyBound,finishBody,bodyRun,bodyHalt,bodyStore⟩ := downItem_executes consumed accepted tail
        (by simp [consumed,status]) consumedWork (by simp [consumed,e18]) (by simp [consumed,e19])
        (by simp [consumed,e20]) (by simp [consumed,e21]) (by simp [consumed,e23]) (by simp [consumed,e24])
        (by simp [consumed,e25]) (by simp [consumed,e26]) (by simp [consumed,e30]) (by simp [consumed,e31])
        (by simp [consumed,e32]) (by simp [consumed,e33]) (by simp [consumed,e37]) (by simp [consumed,e38])
        vista weights length (by simp [consumed,nodeInput]) (by simp [consumed,table])
        (by simp [consumed,weightInput]) (by simp [consumed,nodeCount]) rounds (by simp [consumed,level])
      let nextWeights := Executable.propagateLevel vista weights rounds
      let middle := Function.update (Function.update consumed 22 rounds.bits) 35
        ((Encoding.array Encoding.natural).encode nextWeights)
      have middleWork (i : Fin 40) (small : i.val<17) (different : i≠1) : middle i=[] := by
        have n22 : i≠22 := by intro same;subst i;norm_num at small
        have n35 : i≠35 := by intro same;subst i;norm_num at small
        simp [middle,n22,n35,consumedWork i small different]
      obtain ⟨tailTime,tailBound,finishTail,tailRun,tailHalt,tailStore⟩ := ih middle
        (by simp [middle,consumed,status]) middleWork (by simp [middle,consumed,e18])
        (by simp [middle,consumed,e19]) (by simp [middle,consumed,e20]) (by simp [middle,consumed,e21])
        (by simp [middle,consumed,e23]) (by simp [middle,consumed,e24]) (by simp [middle,consumed,e25])
        (by simp [middle,consumed,e26]) (by simp [middle,consumed,e30]) (by simp [middle,consumed,e31])
        (by simp [middle,consumed,e32]) (by simp [middle,consumed,e33])
        (by simp [middle,consumed,e37]) (by simp [middle,consumed,e38]) nextWeights
        (by simpa only [nextWeights,Executable.propagateLevel_size] using length)
        (by simp [middle,consumed,nodeInput]) (by simp [middle,consumed,table]) (by simp [middle])
        (by simp [middle,consumed,nodeCount]) (by simp [middle]) bits (by simp [middle,consumed])
        (by simpa using countEq)
      have firstRun := repeat_iteration (39:Fin 40) downItem store bit bits counter bodyTime finishBody bodyRun bodyHalt
      have final : downLoopStore middle vista rounds nextWeights=downLoopStore store vista (rounds+1) weights := by
        funext i
        by_cases i22 : i=22 <;> by_cases i35 : i=35 <;> by_cases i39 : i=39 <;>
          simp [downLoopStore,Executable.propagateDown_succ,middle,consumed,nextWeights,i22,i35,i39]
      refine ⟨bodyTime+2+tailTime,?_,finishTail,?_,tailHalt,tailStore.trans final⟩
      · have b17 : consumed 17=store 17 := by simp [consumed]
        have m17 : middle 17=store 17 := by simp [middle,consumed]
        rw [b17] at bodyBound
        rw [m17] at tailBound
        change _ ≤ downItemBudget vista rounds (store 17).length weights+2+
          downLoopBudget vista (store 17).length rounds nextWeights
        omega
      · rw [Machine.run_add,firstRun,Option.bind_some,bodyStore]
        exact tailRun

end Counting.StackMachine.AuditPropagation
