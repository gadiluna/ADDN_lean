import Counting.ExternalMatchingVariableStep
import Counting.ExternalMatchingCompletionLoop

namespace Counting.External.MatchingMachine
open StackMachine StackMachine.Routine
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

def variableRows (first second third : Nat) : Nat → List (List Nat)
  | 0 => []
  | count+1 => pairRows first second third++variableRows (first+1) (second+1) (third+1) count

def emitVariableRun (extra : Nat) (w : PortWorkspace extra) : Routine (extra+11) :=
  forEach (w 12) (emitVariableStep (extra+1) w.edge)

def variableRunResult (extra : Nat) (w : PortWorkspace extra) (store : Fin (extra+13) → List Bool) (count : Nat) :=
  Function.update (Function.update (Function.update (Function.update (Function.update store (w 12) [])
    (w 0) (List.replicate count true++store (w 0))) (w 1) (List.replicate count true++store (w 1)))
    (w 2) (List.replicate count true++store (w 2)))
    (w 6) ((Encoding.sequence (Encoding.list Encoding.natural)
      (variableRows (store (w 0)).length (store (w 1)).length (store (w 2)).length count)).reverse++store (w 6))

theorem emitVariableRun_executes (extra : Nat) (w : PortWorkspace extra) (count limit : Nat)
    (store : Fin (extra+13) → List Bool)
    (counter : store (w 12)=List.replicate count true)
    (bounded : (store (w 0)).length+(store (w 1)).length+(store (w 2)).length+3*count ≤ limit)
    (empty : ∀ i∈([3,4,5,7,8,9,10,11] : List (Fin 13)),store (w i)=[]) :
    ∃ time ≤ count*(410*(limit+1)^2+2)+1,
      Executes (emitVariableRun extra w) store time (variableRunResult extra w store count) := by
  induction count generalizing store with
  | zero =>
    obtain ⟨ran,halted⟩ := repeat_empty (w 12) (emitVariableStep (extra+1) w.edge) store counter
    have unchanged : variableRunResult extra w store 0=store := by
      simp only [variableRunResult,variableRows,Encoding.sequence,List.reverse_nil,List.nil_append,List.replicate_zero]
      have counterEmpty : store (w 12)=[] := counter
      rw [←counterEmpty,Function.update_eq_self,Function.update_eq_self,Function.update_eq_self,Function.update_eq_self,Function.update_eq_self]
    exact ⟨1,by simp,⟨1,store⟩,ran,halted,unchanged.symm⟩
  | succ count ih =>
    let consumed := Function.update store (w 12) (List.replicate count true)
    have consumedEmpty (i : Fin 12) (member : i∈([3,4,5,7,8,9,10,11] : List (Fin 12))) :
        consumed (w.edge i)=[] := by
      have hi : i.val<12 := i.isLt
      have mem : (⟨i.val,by omega⟩ : Fin 13)∈([3,4,5,7,8,9,10,11] : List (Fin 13)) := by
        fin_cases i <;> simp_all
      simpa [PortWorkspace.edge,consumed,w.injective.eq_iff,show i.val≠12 by omega,Fin.ext_iff] using empty _ mem
    obtain ⟨bodyTime,bodyBound,bodyFinish,bodyRun,bodyHalt,bodyStore⟩ := emitVariableStep_executes (extra+1) w.edge consumed consumedEmpty
    let next := variableStepResult (extra+1) w.edge consumed
    have nextCounter : next (w 12)=List.replicate count true := by simp [next,variableStepResult,PortWorkspace.edge,consumed,w.injective.eq_iff]
    have nextBound : (next (w 0)).length+(next (w 1)).length+(next (w 2)).length+3*count ≤ limit := by
      simp [next,variableStepResult,PortWorkspace.edge,consumed,w.injective.eq_iff]
      omega
    have nextEmpty (i : Fin 13) (member : i∈([3,4,5,7,8,9,10,11] : List (Fin 13))) : next (w i)=[] := by
      have a : i≠0 := by intro eq;subst i;simp at member
      have b : i≠1 := by intro eq;subst i;simp at member
      have c : i≠2 := by intro eq;subst i;simp at member
      have d : i≠6 := by intro eq;subst i;simp at member
      have e : i≠12 := by intro eq;subst i;simp at member
      simpa [next,variableStepResult,PortWorkspace.edge,consumed,w.injective.eq_iff,a,b,c,d,e] using empty i member
    obtain ⟨tailTime,tailBound,tailFinish,tailRun,tailHalt,tailStore⟩ := ih next nextCounter nextBound nextEmpty
    have firstRun := repeat_iteration (w 12) (emitVariableStep (extra+1) w.edge) store true (List.replicate count true)
      (by simpa only [List.replicate_succ] using counter) bodyTime bodyFinish bodyRun bodyHalt
    change Machine.run (step (emitVariableRun extra w).program) (bodyTime+2) ⟨0,store⟩=some ⟨0,bodyFinish.store⟩ at firstRun
    have bodyLimit : bodyTime ≤ 410*(limit+1)^2 := by
      have boundAs : bodyTime ≤ 410*((store (w 0)).length+(store (w 1)).length+(store (w 2)).length+1)^2 := by
        simpa [PortWorkspace.edge,consumed,w.injective.eq_iff] using bodyBound
      apply boundAs.trans
      apply Nat.mul_le_mul_left
      apply Nat.pow_le_pow_left
      omega
    refine ⟨bodyTime+2+tailTime,?_,tailFinish,?_,tailHalt,?_⟩
    · nlinarith only [bodyLimit,tailBound]
    · rw [Machine.run_add,firstRun,Option.bind_some,bodyStore]
      exact tailRun
    · rw [tailStore]
      funext r
      by_cases c : r=w 12
      · subst r;simp [variableRunResult,w.injective.eq_iff]
      · by_cases a : r=w 0
        · subst r
          simp [variableRunResult,next,variableStepResult,PortWorkspace.edge,consumed,w.injective.eq_iff,List.replicate_succ,replicate_append_cons]
        · by_cases b : r=w 1
          · subst r
            simp [variableRunResult,next,variableStepResult,PortWorkspace.edge,consumed,w.injective.eq_iff,List.replicate_succ,replicate_append_cons]
          · by_cases d : r=w 2
            · subst r
              simp [variableRunResult,next,variableStepResult,PortWorkspace.edge,consumed,w.injective.eq_iff,List.replicate_succ,replicate_append_cons]
            · by_cases o : r=w 6
              · subst r
                simp [variableRunResult,next,variableStepResult,PortWorkspace.edge,consumed,w.injective.eq_iff,variableRows,sequence_append,
                  List.reverse_append,List.append_assoc]
              · simp [variableRunResult,next,variableStepResult,PortWorkspace.edge,consumed,c,a,b,d,o]

end Counting.External.MatchingMachine
