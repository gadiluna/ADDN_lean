import Counting.ExternalMatchingVariableBounds

namespace Counting.External.MatchingMachine
open StackMachine StackMachine.Routine
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

abbrev VariableOuterWorkspace (extra : Nat) := Fin 16 ↪ Fin (extra+16)
def VariableOuterWorkspace.block (w : VariableOuterWorkspace extra) : VariableWorkspace (extra+1) :=
  (⟨fun i=>⟨i.val,by omega⟩,by intro a b h;exact Fin.ext (congrArg (fun i : Fin 16=>i.val) h)⟩ : Fin 15 ↪ Fin 16).trans w

def variableBlocksRows (first third normal : Nat) : Nat → List (List Nat)
  | 0 => []
  | count+1 => variableBlockRows first third normal++variableBlocksRows (first+normal+1) (third+normal+1) normal count

def emitVariables (extra : Nat) (w : VariableOuterWorkspace extra) : Routine (extra+14) :=
  forEach (w 15) (variableBlock (extra+1) w.block)

def variablesResult (extra : Nat) (w : VariableOuterWorkspace extra) (store : Fin (extra+16) → List Bool) (count : Nat) :=
  Function.update (Function.update (Function.update (Function.update store (w 15) [])
    (w 0) (List.replicate (count*((store (w 13)).length+1)) true++store (w 0)))
    (w 2) (List.replicate (count*((store (w 13)).length+1)) true++store (w 2)))
    (w 6) ((Encoding.sequence (Encoding.list Encoding.natural)
      (variableBlocksRows (store (w 0)).length (store (w 2)).length (store (w 13)).length count)).reverse++store (w 6))

theorem emitVariables_executes (extra : Nat) (w : VariableOuterWorkspace extra) (count limit : Nat)
    (store : Fin (extra+16) → List Bool)
    (counter : store (w 15)=List.replicate count true)
    (normal : store (w 13)=List.replicate (store (w 13)).length true)
    (bounded : (store (w 0)).length+(store (w 2)).length+(store (w 13)).length+
      2*count*((store (w 13)).length+1) ≤ limit)
    (empty : ∀ i∈([1,3,4,5,7,8,9,10,11,12,14] : List (Fin 16)),store (w i)=[]) :
    ∃ time ≤ count*(8000*(limit+1)^3+2)+1,
      Executes (emitVariables extra w) store time (variablesResult extra w store count) := by
  induction count generalizing store with
  | zero =>
    obtain ⟨ran,halted⟩ := repeat_empty (w 15) (variableBlock (extra+1) w.block) store counter
    have unchanged : variablesResult extra w store 0=store := by
      simp only [variablesResult,variableBlocksRows,Encoding.sequence,List.reverse_nil,List.nil_append,List.replicate_zero,Nat.zero_mul]
      have counterEmpty : store (w 15)=[] := counter
      rw [←counterEmpty,Function.update_eq_self,Function.update_eq_self,Function.update_eq_self,Function.update_eq_self]
    exact ⟨1,by simp,⟨1,store⟩,ran,halted,unchanged.symm⟩
  | succ count ih =>
    let consumed := Function.update store (w 15) (List.replicate count true)
    have consumedNormal : consumed (w.block 13)=List.replicate (consumed (w.block 13)).length true := by
      simpa [consumed,VariableOuterWorkspace.block,w.injective.eq_iff] using normal
    have consumedEmpty (i : Fin 15) (member : i∈([1,3,4,5,7,8,9,10,11,12,14] : List (Fin 15))) : consumed (w.block i)=[] := by
      have hi : i.val<15 := i.isLt
      have mem : (⟨i.val,by omega⟩ : Fin 16)∈([1,3,4,5,7,8,9,10,11,12,14] : List (Fin 16)) := by
        fin_cases i <;> simp at member ⊢
      simpa [consumed,VariableOuterWorkspace.block,w.injective.eq_iff,Fin.ext_iff,show i.val≠15 by omega] using empty _ mem
    obtain ⟨bodyTime,bodyBound,bodyFinish,bodyRun,bodyHalt,bodyStore⟩ := variableBlock_executes (extra+1) w.block consumed consumedNormal consumedEmpty
    let next := variableBlockResult (extra+1) w.block consumed
    have nextCounter : next (w 15)=List.replicate count true := by simp [next,variableBlockResult,VariableOuterWorkspace.block,consumed,w.injective.eq_iff]
    have nextNormal : next (w 13)=List.replicate (next (w 13)).length true := by
      simpa [next,variableBlockResult,VariableOuterWorkspace.block,consumed,w.injective.eq_iff] using normal
    have nextBound : (next (w 0)).length+(next (w 2)).length+(next (w 13)).length+
        2*count*((next (w 13)).length+1) ≤ limit := by
      simp [next,variableBlockResult,VariableOuterWorkspace.block,consumed,w.injective.eq_iff]
      nlinarith only [bounded]
    have nextEmpty (i : Fin 16) (member : i∈([1,3,4,5,7,8,9,10,11,12,14] : List (Fin 16))) : next (w i)=[] := by
      have a : i≠0 := by intro eq;subst i;simp at member
      have b : i≠2 := by intro eq;subst i;simp at member
      have c : i≠6 := by intro eq;subst i;simp at member
      have d : i≠15 := by intro eq;subst i;simp at member
      simpa [next,variableBlockResult,VariableOuterWorkspace.block,consumed,w.injective.eq_iff,a,b,c,d] using empty i member
    obtain ⟨tailTime,tailBound,tailFinish,tailRun,tailHalt,tailStore⟩ := ih next nextCounter nextNormal nextBound nextEmpty
    have firstRun := repeat_iteration (w 15) (variableBlock (extra+1) w.block) store true (List.replicate count true)
      (by simpa only [List.replicate_succ] using counter) bodyTime bodyFinish bodyRun bodyHalt
    change Machine.run (step (emitVariables extra w).program) (bodyTime+2) ⟨0,store⟩=some ⟨0,bodyFinish.store⟩ at firstRun
    have bodyLimit : bodyTime ≤ 8000*(limit+1)^3 := by
      apply bodyBound.trans
      apply (variableBlockCost_le _ _ _).trans
      apply Nat.mul_le_mul_left
      apply Nat.pow_le_pow_left
      simp [consumed,VariableOuterWorkspace.block,w.injective.eq_iff]
      omega
    refine ⟨bodyTime+2+tailTime,?_,tailFinish,?_,tailHalt,?_⟩
    · nlinarith only [bodyLimit,tailBound]
    · rw [Machine.run_add,firstRun,Option.bind_some,bodyStore]
      exact tailRun
    · rw [tailStore]
      funext r
      by_cases c : r=w 15
      · subst r;simp [variablesResult,w.injective.eq_iff]
      · by_cases a : r=w 0
        · subst r
          simp [variablesResult,next,variableBlockResult,VariableOuterWorkspace.block,consumed,w.injective.eq_iff,
            ←List.append_assoc,Nat.add_mul,Nat.add_assoc]
        · by_cases b : r=w 2
          · subst r
            simp [variablesResult,next,variableBlockResult,VariableOuterWorkspace.block,consumed,w.injective.eq_iff,
              ←List.append_assoc,Nat.add_mul,Nat.add_assoc]
          · by_cases o : r=w 6
            · subst r
              simp [variablesResult,next,variableBlockResult,VariableOuterWorkspace.block,consumed,w.injective.eq_iff,
                variableBlocksRows,sequence_append,List.reverse_append,List.append_assoc,Nat.add_comm,Nat.add_left_comm]
            · simp [variablesResult,next,variableBlockResult,VariableOuterWorkspace.block,consumed,c,a,b,o]

end Counting.External.MatchingMachine
