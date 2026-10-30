import Counting.ExternalMatchingVariablePrepare

namespace Counting.External.MatchingMachine
open StackMachine StackMachine.Routine
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

def variableBlockRows (first third count : Nat) : List (List Nat) :=
  variableRows first (first+1) third count++pairRows (first+count) first (third+count)

def variableBlock (extra : Nat) (w : VariableWorkspace extra) : Routine (extra+13) :=
  sequence (variablePrepare extra w)
    (sequence (emitVariableRun (extra+2) w.port)
      (sequence (variableWrap extra w)
        (sequence (emitVariableStep (extra+3) w.port.edge) (sequence (clear (w 1)) (clear (w 14))))))

def variableBlockCost (first third count : Nat) :=
  count*(410*(2*first+third+3*count+2)^2+2)+410*(2*first+third+2*count+1)^2+18*first+6*count+24

def variableBlockResult (extra : Nat) (w : VariableWorkspace extra) (store : Fin (extra+15) → List Bool) :=
  Function.update (Function.update (Function.update store (w 0)
    (List.replicate ((store (w 13)).length+1) true++store (w 0))) (w 2)
    (List.replicate ((store (w 13)).length+1) true++store (w 2))) (w 6)
    ((Encoding.sequence (Encoding.list Encoding.natural)
      (variableBlockRows (store (w 0)).length (store (w 2)).length (store (w 13)).length)).reverse++store (w 6))

theorem variableBlock_executes (extra : Nat) (w : VariableWorkspace extra) (store : Fin (extra+15) → List Bool)
    (unary : store (w 13)=List.replicate (store (w 13)).length true)
    (empty : ∀ i∈([1,3,4,5,7,8,9,10,11,12,14] : List (Fin 15)),store (w i)=[]) :
    ∃ time ≤ variableBlockCost (store (w 0)).length (store (w 2)).length (store (w 13)).length,
      Executes (variableBlock extra w) store time (variableBlockResult extra w store) := by
  let a := (store (w 0)).length
  let c := (store (w 2)).length
  let count := (store (w 13)).length
  let prepared := variablePrepared extra w store
  have prep := variablePrepare_executes extra w store (empty 1 (by decide)) (empty 9 (by decide))
    (empty 12 (by decide)) (empty 14 (by decide))
  have loopEmpty (i : Fin 13) (member : i∈([3,4,5,7,8,9,10,11] : List (Fin 13))) : prepared (w.port i)=[] := by
    have mem : (⟨i.val,by omega⟩ : Fin 15)∈([1,3,4,5,7,8,9,10,11,12,14] : List (Fin 15)) := by fin_cases i <;> simp at member ⊢
    have a1 : i.val≠1 := by fin_cases i <;> simp at member ⊢
    have a12 : i.val≠12 := by fin_cases i <;> simp at member ⊢
    have a14 : i.val≠14 := by omega
    simpa [prepared,variablePrepared,RowWorkspace.port,w.injective.eq_iff,Fin.ext_iff,a1,a12,a14] using empty _ mem
  obtain ⟨loopTime,loopBound,loopRun⟩ := emitVariableRun_executes (extra+2) w.port count
    (2*a+c+3*count+1) prepared
    (by simpa [prepared,variablePrepared,RowWorkspace.port] using unary)
    (by simp [prepared,variablePrepared,RowWorkspace.port,w.injective.eq_iff,a,c];omega) loopEmpty
  let looped := variableRunResult (extra+2) w.port prepared count
  have loopedNeighbor : looped (w 1)=List.replicate count true++true::store (w 0) := by
    simp [looped,variableRunResult,prepared,variablePrepared,RowWorkspace.port,w.injective.eq_iff]
  have loopedBase : looped (w 14)=store (w 0) := by
    simp [looped,variableRunResult,prepared,variablePrepared,RowWorkspace.port,w.injective.eq_iff]
  have loopedFirst : looped (w 0)=List.replicate count true++store (w 0) := by
    simp [looped,variableRunResult,prepared,variablePrepared,RowWorkspace.port,w.injective.eq_iff]
  have loopedThird : looped (w 2)=List.replicate count true++store (w 2) := by
    simp [looped,variableRunResult,prepared,variablePrepared,RowWorkspace.port,w.injective.eq_iff]
  have wrapped := variableWrap_executes extra w looped
    (by simp [looped,variableRunResult,prepared,variablePrepared,RowWorkspace.port,w.injective.eq_iff,empty 9 (by decide)])
  let closed := Function.update looped (w 1) (store (w 0))
  have wrap : Executes (variableWrap extra w) looped (6*a+count+5) closed := by
    simpa only [loopedNeighbor,loopedBase,List.length_append,List.length_replicate,List.length_cons,closed,
      show count+((store (w 0)).length+1)+5*(store (w 0)).length+4=6*a+count+5 by dsimp [a];omega] using wrapped
  have stepEmpty (i : Fin 12) (member : i∈([3,4,5,7,8,9,10,11] : List (Fin 12))) : closed (w.port.edge i)=[] := by
    have mem : (⟨i.val,by omega⟩ : Fin 15)∈([1,3,4,5,7,8,9,10,11,12,14] : List (Fin 15)) := by fin_cases i <;> simp at member ⊢
    have a0 : i.val≠0 := by fin_cases i <;> simp at member ⊢
    have a1 : i.val≠1 := by fin_cases i <;> simp at member ⊢
    have a2 : i.val≠2 := by fin_cases i <;> simp at member ⊢
    have a6 : i.val≠6 := by fin_cases i <;> simp at member ⊢
    have a12 : i.val≠12 := by omega
    have a14 : i.val≠14 := by omega
    simpa [closed,looped,variableRunResult,prepared,variablePrepared,PortWorkspace.edge,RowWorkspace.port,
      w.injective.eq_iff,Fin.ext_iff,a0,a1,a2,a6,a12,a14] using empty _ mem
  obtain ⟨stepTime,stepBound,stepRun⟩ := emitVariableStep_executes (extra+3) w.port.edge closed stepEmpty
  let stepped := variableStepResult (extra+3) w.port.edge closed
  have steppedNeighbor : stepped (w 1)=true::store (w 0) := by
    simp [stepped,variableStepResult,PortWorkspace.edge,RowWorkspace.port,closed,w.injective.eq_iff]
  have steppedBase : stepped (w 14)=store (w 0) := by
    simp [stepped,variableStepResult,PortWorkspace.edge,RowWorkspace.port,closed,w.injective.eq_iff,loopedBase]
  have clear1 := clear_executes (w 1) stepped
  have clear14 := clear_executes (w 14) (Function.update stepped (w 1) [])
  have cleanup := clear1.sequence clear14
  have cleanupTime : (stepped (w 1)).length+1+1+((Function.update stepped (w 1) [] (w 14)).length+1)=2*a+4 := by
    simp [steppedNeighbor,steppedBase,w.injective.eq_iff,a];omega
  rw [cleanupTime] at cleanup
  have final : Function.update (Function.update stepped (w 1) []) (w 14) []=variableBlockResult extra w store := by
    funext r
    by_cases a1 : r=w 1
    · subst r;simp [variableBlockResult,w.injective.eq_iff,empty 1 (by decide)]
    · by_cases a14 : r=w 14
      · subst r;simp [variableBlockResult,w.injective.eq_iff,empty 14 (by decide)]
      · by_cases a0 : r=w 0
        · subst r
          simp [variableBlockResult,stepped,variableStepResult,PortWorkspace.edge,RowWorkspace.port,closed,
            loopedFirst,w.injective.eq_iff,List.replicate_succ,count]
        · by_cases a2 : r=w 2
          · subst r
            simp [variableBlockResult,stepped,variableStepResult,PortWorkspace.edge,RowWorkspace.port,closed,
              loopedThird,w.injective.eq_iff,List.replicate_succ,count]
          · by_cases a6 : r=w 6
            · subst r
              simp [variableBlockResult,variableBlockRows,stepped,variableStepResult,PortWorkspace.edge,RowWorkspace.port,closed,
                looped,variableRunResult,prepared,variablePrepared,w.injective.eq_iff,sequence_append,
                List.reverse_append,List.append_assoc,count,Nat.add_comm]
            · by_cases a12 : r=w 12
              · subst r
                simp [variableBlockResult,stepped,variableStepResult,PortWorkspace.edge,RowWorkspace.port,closed,
                  looped,variableRunResult,w.injective.eq_iff,empty 12 (by decide)]
              · simp [variableBlockResult,stepped,variableStepResult,PortWorkspace.edge,RowWorkspace.port,closed,
                  looped,variableRunResult,prepared,variablePrepared,a1,a14,a0,a2,a6,a12]
  rw [final] at cleanup
  have combined := prep.sequence (loopRun.sequence (wrap.sequence (stepRun.sequence cleanup)))
  refine ⟨10*a+5*count+10+1+(loopTime+1+(6*a+count+5+1+(stepTime+1+(2*a+4)))),?_,combined⟩
  have stepLimit : stepTime ≤ 410*(2*a+c+2*count+1)^2 := by
    simpa [PortWorkspace.edge,RowWorkspace.port,closed,w.injective.eq_iff,loopedFirst,loopedThird,a,c,
      Nat.add_assoc,Nat.add_left_comm,Nat.add_comm,two_mul] using stepBound
  change _ ≤ variableBlockCost a c count
  unfold variableBlockCost
  have loopLimit : loopTime ≤ count*(410*(2*a+c+3*count+2)^2+2)+1 := by
    simpa only [Nat.add_assoc,show (1:Nat)+1=2 from rfl] using loopBound
  omega

end Counting.External.MatchingMachine
