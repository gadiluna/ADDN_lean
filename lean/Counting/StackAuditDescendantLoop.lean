import Counting.StackAuditDescendantItem

namespace Counting.StackMachine.AuditDescendant
open Routine
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

def countLoop : Routine 38 := forEach 30 countCurrent

def countLoopResult (store : Store 38) (vista : Executable.Vista)
    (steps last ancestor start count : Nat) : Store 38 :=
  Function.update (Function.update (Function.update (Function.update store 30 []) 36
    (List.replicate count true++store 36)) 37 (start+count+1).bits) 39
      (List.replicate (Executable.descendantCountRange vista steps last ancestor start count) true++store 39)

/-- A physical bounded table scan accumulates exactly the selected
descendant count. Its explicit iteration budget is consumed, and all other
persistent data are preserved. -/
theorem countLoop_executes (store : Store 38) (vista : Executable.Vista)
    (start last ancestor : Nat) (steps bits : List Bool)
    (inside : start+bits.length ≤ vista.nodes.size)
    (source : store 17=Encoding.sequence Encoding.node vista.nodes.toList)
    (indexAt : (store 36).length=start) (current : store 37=(start+1).bits)
    (lastAt : store 34=last.bits) (target : store 29=(ancestor+1).bits)
    (stepBudget : store 38=steps) (counter : store 30=bits) (flag : store 35=[])
    (empty : ∀ r : Fin 40,r.val ≤ 28 → r≠17 → store r=[]) :
    ∃ time ≤ bits.length*(15000000000*((store 17).length+steps.length+
        (ancestor+1).size+last.size+1)^5+2)+1,
      Executes countLoop store time
        (countLoopResult store vista steps.length last ancestor start bits.length) := by
  induction bits generalizing store start with
  | nil=>
    obtain ⟨ran,halted⟩:=repeat_empty (30:Fin 40) countCurrent store counter
    have final : countLoopResult store vista steps.length last ancestor start 0=store := by
      simp only [countLoopResult,List.replicate_zero,List.nil_append,Nat.add_zero,
        Executable.descendantCountRange_zero]
      rw [←current,←counter]
      simp only [Function.update_eq_self]
    exact ⟨1,by simp,⟨1,store⟩,ran,halted,final.symm⟩
  | cons bit bits ih=>
    let consumed:=Function.update store 30 bits
    have validIndex : start < vista.nodes.size := by simp only [List.length_cons] at inside;omega
    let index : Fin vista.nodes.size:=⟨start,validIndex⟩
    have consumedEmpty (r : Fin 40) (small : r.val ≤ 28) (different : r≠17) : consumed r=[] := by
      have n30 : r≠30 := by intro same;subst r;norm_num at small
      simp [consumed,n30,empty r small different]
    obtain ⟨bodyTime,bodyBound,bodyFinish,bodyRun,bodyHalt,bodyStore⟩:=countCurrent_executes consumed vista index last ancestor steps
      (by simp [consumed,source]) (by simpa [consumed,index] using indexAt)
      (by simp [consumed,index,current]) (by simp [consumed,lastAt]) (by simp [consumed,target])
      (by simp [consumed,stepBudget]) (by simp [consumed,flag]) consumedEmpty
    let hit:=Executable.descendantSelected vista steps.length last ancestor start
    let middle:=countItemResult consumed start hit
    have bodyResult : bodyFinish.store=middle := bodyStore
    have middleEmpty (r : Fin 40) (small : r.val ≤ 28) (different : r≠17) : middle r=[] := by
      have n36 : r≠36 := by intro same;subst r;norm_num at small
      have n37 : r≠37 := by intro same;subst r;norm_num at small
      have n39 : r≠39 := by intro same;subst r;norm_num at small
      simp [middle,countItemResult,n36,n37,n39,consumedEmpty r small different]
    obtain ⟨tailTime,tailBound,tailFinish,tailRun,tailHalt,tailStore⟩:=ih middle (start+1)
      (by simp only [List.length_cons] at inside;omega)
      (by simp [middle,countItemResult,consumed,source])
      (by simp [middle,countItemResult,consumed,indexAt])
      (by simp [middle,countItemResult])
      (by simp [middle,countItemResult,consumed,lastAt])
      (by simp [middle,countItemResult,consumed,target])
      (by simp [middle,countItemResult,consumed,stepBudget])
      (by simp [middle,countItemResult,consumed])
      (by simp [middle,countItemResult,consumed,flag]) middleEmpty
    have first:=repeat_iteration (30:Fin 40) countCurrent store bit bits counter bodyTime bodyFinish bodyRun bodyHalt
    have final : countLoopResult middle vista steps.length last ancestor (start+1) bits.length=
        countLoopResult store vista steps.length last ancestor start (bit::bits).length := by
      funext r
      by_cases r30:r=30 <;> by_cases r36:r=36 <;> by_cases r37:r=37 <;> by_cases r39:r=39 <;>
        simp [countLoopResult,middle,countItemResult,consumed,Executable.descendantCountRange_succ,
          hit,r30,r36,r37,r39,←List.append_assoc,List.replicate_succ',
          Nat.add_comm,Nat.add_left_comm] <;> simp only [List.append_assoc,List.singleton_append]
    have sourceSame : (consumed 17).length=(store 17).length := by simp [consumed]
    have tableSame : (middle 17).length=(store 17).length := by simp [middle,countItemResult,consumed]
    rw [sourceSame] at bodyBound
    rw [tableSame] at tailBound
    refine ⟨bodyTime+2+tailTime,?_,tailFinish,?_,tailHalt,tailStore.trans final⟩
    · simp only [List.length_cons]
      nlinarith only [bodyBound,tailBound]
    · change Machine.run (step (forEach 30 countCurrent).program) (bodyTime+2+tailTime)
        ⟨0,store⟩=some tailFinish
      rw [Machine.run_add,first,Option.bind_some,bodyResult]
      exact tailRun

end Counting.StackMachine.AuditDescendant
