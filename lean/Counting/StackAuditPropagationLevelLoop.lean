import Counting.AuditPropagationLevelOrder

namespace Counting.StackMachine.AuditPropagation
open Routine EncodingPrograms
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000

abbrev levelLoop : Routine 38 := forEach 32 levelItem

def levelLoopBudget (vista : Executable.Vista) (r tableLength start : Nat) : Nat → Array Nat → Nat
  | 0,_ => 1
  | count+1,weights =>
      30000*(tableLength+(Encoding.vista.encode vista).length+
        ((Encoding.array Encoding.natural).encode weights).length+r.size+(r+1).size+start+2)^5+2+
      levelLoopBudget vista r tableLength (start+1) count (levelChoiceWeights vista r start weights)

def levelLoopStore (store : Store 38) (vista : Executable.Vista) (r start count : Nat) (weights : Array Nat) : Store 38 :=
  Function.update (Function.update (Function.update store 32 []) 18 (List.replicate (start+count) true)) 35
    ((Encoding.array Encoding.natural).encode (levelScan vista r start count weights))

/-- The actual bounded node loop realizes all selected writes in order.
Its budget records the serialized sizes of the actual intermediate arrays;
a separate size theorem supplies the uniform polynomial bound. -/
theorem levelLoop_executes (store : Store 38) (accepted : Bool) (tail : List Bool)
    (status : store 1=accepted::tail)
    (work : ∀ i : Fin 40,i.val<17 → i≠1 → store i=[])
    (e19 : store 19=[]) (e20 : store 20=[]) (e21 : store 21=[])
    (e23 : store 23=[]) (e24 : store 24=[]) (e25 : store 25=[])
    (e26 : store 26=[]) (e31 : store 31=[]) (e33 : store 33=[])
    (e37 : store 37=[]) (e38 : store 38=[])
    (vista : Executable.Vista) (weights : Array Nat) (length : weights.size=vista.nodes.size)
    (nodeInput : store 34=Encoding.vista.encode vista)
    (table : store 17=Encoding.sequence Encoding.node vista.nodes.toList++Encoding.natural.encode vista.bottom)
    (weightInput : store 35=(Encoding.array Encoding.natural).encode weights)
    (r start count : Nat) (inside : start+count ≤ vista.nodes.size)
    (level : store 22=(r+1).bits) (query : store 30=r.bits)
    (indexCounter : store 18=List.replicate start true)
    (bits : List Bool) (counter : store 32=bits) (countEq : bits.length=count) :
    ∃ time ≤ levelLoopBudget vista r (store 17).length start count weights,
      Executes levelLoop store time (levelLoopStore store vista r start count weights) := by
  induction count generalizing store start weights bits with
  | zero =>
    have empty : store 32=[] := counter.trans (List.length_eq_zero_iff.mp countEq)
    obtain ⟨ran,halted⟩ := repeat_empty (32:Fin 40) levelItem store empty
    have finish : levelLoopStore store vista r start 0 weights=store := by
      simp only [levelLoopStore,levelScan,Nat.add_zero]
      rw [←empty,Function.update_eq_self,←indexCounter,Function.update_eq_self,←weightInput,Function.update_eq_self]
    exact ⟨1,by rfl,⟨1,store⟩,ran,halted,finish.symm⟩
  | succ count ih =>
    cases bits with
    | nil => simp at countEq
    | cons bit bits =>
      have bounded : start<vista.nodes.size := by omega
      let index : Fin vista.nodes.size := ⟨start,bounded⟩
      let consumed := Function.update store 32 bits
      have consumedWork (i : Fin 40) (small : i.val<17) (different : i≠1) : consumed i=[] := by
        have n32 : i≠32 := by intro same;subst i;norm_num at small
        simp [consumed,n32,work i small different]
      obtain ⟨bodyTime,bodyBound,finishBody,bodyRun,bodyHalt,bodyStore⟩ := levelItem_executes consumed accepted tail
        (by simp [consumed,status]) consumedWork (by simp [consumed,e19]) (by simp [consumed,e20])
        (by simp [consumed,e21]) (by simp [consumed,e23]) (by simp [consumed,e24])
        (by simp [consumed,e25]) (by simp [consumed,e26]) (by simp [consumed,e31])
        (by simp [consumed,e33]) (by simp [consumed,e37]) (by simp [consumed,e38])
        vista weights length (by simp [consumed,nodeInput]) (by simp [consumed,table])
        (by simp [consumed,weightInput]) r index (by simp [consumed,level]) (by simp [consumed,query])
        (by simp [consumed,index,indexCounter])
      let nextWeights := levelChoiceWeights vista r start weights
      let middle := Function.update (Function.update consumed 35 ((Encoding.array Encoding.natural).encode nextWeights)) 18
        (List.replicate (start+1) true)
      have middleWork (i : Fin 40) (small : i.val<17) (different : i≠1) : middle i=[] := by
        have n18 : i≠18 := by intro same;subst i;norm_num at small
        have n35 : i≠35 := by intro same;subst i;norm_num at small
        simp [middle,n18,n35,consumedWork i small different]
      obtain ⟨tailTime,tailBound,finishTail,tailRun,tailHalt,tailStore⟩ := ih middle
        (by simp [middle,consumed,status]) middleWork (by simp [middle,consumed,e19])
        (by simp [middle,consumed,e20]) (by simp [middle,consumed,e21]) (by simp [middle,consumed,e23])
        (by simp [middle,consumed,e24]) (by simp [middle,consumed,e25]) (by simp [middle,consumed,e26])
        (by simp [middle,consumed,e31]) (by simp [middle,consumed,e33])
        (by simp [middle,consumed,e37]) (by simp [middle,consumed,e38])
        nextWeights (by simp [nextWeights,length]) (by simp [middle,consumed,nodeInput])
        (by simp [middle,consumed,table]) (by simp [middle]) (start+1) (by omega)
        (by simp [middle,consumed,level]) (by simp [middle,consumed,query]) (by simp [middle])
        bits (by simp [middle,consumed]) (by simpa using countEq)
      have firstRun := repeat_iteration (32:Fin 40) levelItem store bit bits counter bodyTime finishBody bodyRun bodyHalt
      have final : levelLoopStore middle vista r (start+1) count nextWeights=
          levelLoopStore store vista r start (count+1) weights := by
        funext i
        by_cases i18 : i=18 <;> by_cases i32 : i=32 <;> by_cases i35 : i=35 <;>
          simp [levelLoopStore,levelScan,middle,consumed,nextWeights,i18,i32,i35,
            Nat.add_comm,Nat.add_left_comm]
      refine ⟨bodyTime+2+tailTime,?_,finishTail,?_,tailHalt,tailStore.trans final⟩
      · have b1 : consumed 17=store 17 := by simp [consumed]
        have b2 : consumed 34=Encoding.vista.encode vista := by simp [consumed,nodeInput]
        have b3 : consumed 35=(Encoding.array Encoding.natural).encode weights := by simp [consumed,weightInput]
        have m1 : middle 17=store 17 := by simp [middle,consumed]
        rw [b1,b2,b3] at bodyBound
        rw [m1] at tailBound
        change bodyTime ≤ 30000*((store 17).length+(Encoding.vista.encode vista).length+
          ((Encoding.array Encoding.natural).encode weights).length+r.size+(r+1).size+start+2)^5 at bodyBound
        change _ ≤ _+2+levelLoopBudget vista r (store 17).length (start+1) count nextWeights
        omega
      · rw [Machine.run_add,firstRun,Option.bind_some,bodyStore]
        exact tailRun

end Counting.StackMachine.AuditPropagation
