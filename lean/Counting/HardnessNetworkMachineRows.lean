import Counting.HardnessNetworkMachineRow

namespace Counting.HardnessNetworkMachine
open StackMachine StackMachine.Routine
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000

abbrev RowsWorkspace (extra : Nat) := Fin 10 ↪ Fin (extra+10)
def rowsPositions : Fin 9 ↪ Fin 10 := ⟨fun i=>⟨i.val,by omega⟩,by intro a b h;apply Fin.ext;exact congrArg (fun i : Fin 10=>i.val) h⟩
def RowsWorkspace.row (w : RowsWorkspace extra) : RowWorkspace (extra+1) := rowsPositions.trans w

def consecutiveRows (width start : Nat) : Nat → List (List Nat)
  | 0=>[]
  | count+1=>oneHotRow width start::consecutiveRows width (start+1) count

def emitNextRow (extra : Nat) (w : RowsWorkspace extra) : Routine (extra+8) :=
  sequence (emitOneHotRow (extra+1) w.row) (pushBit (w 1) true)

def nextRowResult (w : RowsWorkspace extra) (store : Fin (extra+10) → List Bool) :=
  Function.update (Function.update store (w 2)
    (((Encoding.list Encoding.natural).encode (oneHotRow (store (w 0)).length (store (w 1)).length)).reverse++store (w 2)))
    (w 1) (true::store (w 1))

theorem emitNextRow_executes (extra : Nat) (w : RowsWorkspace extra)
    (store : Fin (extra+10) → List Bool) (inside : (store (w 1)).length<(store (w 0)).length)
    (empty : ∀ i∈([3,4,5,6,7,8] : List (Fin 10)),store (w i)=[]) :
    ∃ time ≤ 100*((store (w 0)).length+(store (w 1)).length+1)^2+2,
      Executes (emitNextRow extra w) store time (nextRowResult w store) := by
  obtain ⟨rowTime,rowBound,rowRun⟩:=emitOneHotRow_executes (extra+1) w.row store inside
    (by intro i member;fin_cases i <;> simp [rowScratch] at member
        all_goals simp [RowsWorkspace.row,rowsPositions,empty])
  let result:=Function.update store (w 2)
    (((Encoding.list Encoding.natural).encode (oneHotRow (store (w 0)).length (store (w 1)).length)).reverse++store (w 2))
  have rowAs : Executes (emitOneHotRow (extra+1) w.row) store rowTime result := rowRun
  have pushing:=pushBit_executes (w 1) true result
  have final : Function.update result (w 1) (true::result (w 1))=nextRowResult w store := by
    simp [result,nextRowResult,w.injective.eq_iff]
  rw [final] at pushing
  exact ⟨rowTime+1+1,by simpa [RowsWorkspace.row,rowsPositions] using Nat.add_le_add_right rowBound 2,rowAs.sequence pushing⟩

def emitConsecutiveRows (extra : Nat) (w : RowsWorkspace extra) : Routine (extra+8) :=
  forEach (w 9) (emitNextRow extra w)

def consecutiveRowsResult (w : RowsWorkspace extra) (store : Fin (extra+10) → List Bool) (count : Nat) :=
  Function.update (Function.update (Function.update store (w 9) [])
    (w 1) (List.replicate count true++store (w 1))) (w 2)
    ((Encoding.sequence (Encoding.list Encoding.natural)
      (consecutiveRows (store (w 0)).length (store (w 1)).length count)).reverse++store (w 2))

theorem true_replicate_append (count : Nat) (tail : List Bool) :
    List.replicate count true++true::tail=true::(List.replicate count true++tail) := by
  calc
    _ = (List.replicate count true++[true])++tail := by simp [List.append_assoc]
    _ = _ := by rw [←List.replicate_succ',List.replicate_succ,List.cons_append]

/-- Emit consecutive path edges. The loop counter is consumed, the column
index advances once per row, and all other registers are preserved. -/
theorem emitConsecutiveRows_executes (extra : Nat) (w : RowsWorkspace extra) (count : Nat)
    (store : Fin (extra+10) → List Bool) (counter : store (w 9)=List.replicate count true)
    (inside : (store (w 1)).length+count ≤ (store (w 0)).length)
    (empty : ∀ i∈([3,4,5,6,7,8] : List (Fin 10)),store (w i)=[]) :
    ∃ time ≤ count*(100*(2*(store (w 0)).length+1)^2+4)+1,
      Executes (emitConsecutiveRows extra w) store time (consecutiveRowsResult w store count) := by
  induction count generalizing store with
  | zero=>
    obtain ⟨ran,halted⟩:=repeat_empty (w 9) (emitNextRow extra w) store counter
    have same : consecutiveRowsResult w store 0=store := by
      simp only [consecutiveRowsResult,consecutiveRows,Encoding.sequence,List.reverse_nil,List.nil_append,List.replicate_zero]
      have nil : store (w 9)=[]:=counter
      rw [←nil,Function.update_eq_self,Function.update_eq_self,Function.update_eq_self]
    exact ⟨1,by simp,⟨1,store⟩,ran,halted,same.symm⟩
  | succ count ih=>
    let consumed:=Function.update store (w 9) (List.replicate count true)
    have consumedInside : (consumed (w 1)).length<(consumed (w 0)).length := by
      simp only [consumed,Function.update_apply,w.injective.eq_iff] at ⊢
      simp only [Fin.reduceEq,ite_false]
      omega
    have consumedEmpty (i : Fin 10) (member : i∈([3,4,5,6,7,8] : List (Fin 10))) : consumed (w i)=[] := by
      have different : i≠9 := by intro eq;subst i;simp at member
      simpa [consumed,w.injective.eq_iff,different] using empty i member
    obtain ⟨bodyTime,bodyBound,bodyFinish,bodyRun,bodyHalt,bodyStore⟩:=
      emitNextRow_executes extra w consumed consumedInside consumedEmpty
    let next:=nextRowResult w consumed
    have nextCounter : next (w 9)=List.replicate count true := by simp [next,nextRowResult,consumed,w.injective.eq_iff]
    have nextInside : (next (w 1)).length+count ≤ (next (w 0)).length := by
      simpa [next,nextRowResult,consumed,w.injective.eq_iff,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using inside
    have nextEmpty (i : Fin 10) (member : i∈([3,4,5,6,7,8] : List (Fin 10))) : next (w i)=[] := by
      have a : i≠1 := by intro eq;subst i;simp at member
      have b : i≠2 := by intro eq;subst i;simp at member
      simpa [next,nextRowResult,w.injective.eq_iff,a,b] using consumedEmpty i member
    obtain ⟨tailTime,tailBound,tailFinish,tailRun,tailHalt,tailStore⟩:=ih next nextCounter nextInside nextEmpty
    have firstRun:=repeat_iteration (w 9) (emitNextRow extra w) store true (List.replicate count true)
      (by simpa only [List.replicate_succ] using counter) bodyTime bodyFinish bodyRun bodyHalt
    change Machine.run (step (emitConsecutiveRows extra w).program) (bodyTime+2) ⟨0,store⟩=some ⟨0,bodyFinish.store⟩ at firstRun
    have widthAt : (next (w 0)).length=(store (w 0)).length := by simp [next,nextRowResult,consumed,w.injective.eq_iff]
    rw [widthAt] at tailBound
    have bodyLimit : bodyTime ≤ 100*(2*(store (w 0)).length+1)^2+2 := by
      apply bodyBound.trans
      apply Nat.add_le_add_right
      apply Nat.mul_le_mul_left
      apply Nat.pow_le_pow_left
      simp only [consumed,Function.update_apply,w.injective.eq_iff,Fin.reduceEq,ite_false]
      omega
    refine ⟨bodyTime+2+tailTime,by nlinarith only [bodyLimit,tailBound],tailFinish,?_,tailHalt,?_⟩
    · rw [Machine.run_add,firstRun,Option.bind_some,bodyStore]
      exact tailRun
    · rw [tailStore]
      funext r
      by_cases e9 : r=w 9
      · subst r;simp [consecutiveRowsResult,w.injective.eq_iff]
      · by_cases e1 : r=w 1
        · subst r;simp [consecutiveRowsResult,next,nextRowResult,consumed,w.injective.eq_iff,List.replicate_succ,true_replicate_append]
        · by_cases e2 : r=w 2
          · subst r;simp [consecutiveRowsResult,next,nextRowResult,consumed,w.injective.eq_iff,consecutiveRows,
              Encoding.sequence,List.reverse_append,List.append_assoc]
          · simp [consecutiveRowsResult,next,nextRowResult,consumed,e9,e1,e2]

end Counting.HardnessNetworkMachine
