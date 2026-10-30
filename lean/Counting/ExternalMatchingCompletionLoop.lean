import Counting.ExternalMatchingRow

namespace Counting.External.MatchingMachine
open StackMachine StackMachine.Routine
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1100000

theorem sequence_append {α : Type} (codec : Encoding.Codec α) (a b : List α) :
    Encoding.sequence codec (a++b)=Encoding.sequence codec a++Encoding.sequence codec b := by
  induction a with
  | nil => rfl
  | cons x xs ih => simp [Encoding.sequence,ih,List.append_assoc]

def completionRows (first second ports : Nat) : Nat → List (List Nat)
  | 0 => []
  | count+1 => portRows first second 0 ports++completionRows (first+1) (second+1) ports count

def emitCompletion (extra : Nat) (w : RowWorkspace extra) : Routine (extra+13) :=
  forEach (w 14) (emitRow extra w)

def completionResult (extra : Nat) (w : RowWorkspace extra) (store : Fin (extra+15) → List Bool) (count : Nat) :=
  Function.update (Function.update (Function.update (Function.update store (w 14) [])
    (w 0) (List.replicate count true++store (w 0))) (w 1) (List.replicate count true++store (w 1)))
    (w 6) ((Encoding.sequence (Encoding.list Encoding.natural)
      (completionRows (store (w 0)).length (store (w 1)).length (store (w 13)).length count)).reverse++store (w 6))

theorem replicate_append_cons (count : Nat) (tail : List Bool) :
    List.replicate count true++true::tail=true::(List.replicate count true++tail) := by
  calc
    _ = (List.replicate count true++[true])++tail := by simp [List.append_assoc]
    _ = _ := by rw [←List.replicate_succ',List.replicate_succ,List.cons_append]

theorem emitCompletion_executes (extra : Nat) (w : RowWorkspace extra) (count limit : Nat)
    (store : Fin (extra+15) → List Bool)
    (counter : store (w 14)=List.replicate count true)
    (ports : store (w 13)=List.replicate (store (w 13)).length true)
    (bounded : (store (w 0)).length+(store (w 1)).length+(store (w 13)).length+2*count ≤ limit)
    (empty : ∀ i∈([2,3,4,5,7,8,9,10,11,12] : List (Fin 15)),store (w i)=[]) :
    ∃ time ≤ count*(320*(limit+1)^3+2)+1,
      Executes (emitCompletion extra w) store time (completionResult extra w store count) := by
  induction count generalizing store with
  | zero =>
    obtain ⟨ran,halted⟩ := repeat_empty (w 14) (emitRow extra w) store counter
    have unchanged : completionResult extra w store 0=store := by
      simp only [completionResult,completionRows,Encoding.sequence,List.reverse_nil,List.nil_append,List.replicate_zero]
      have counterEmpty : store (w 14)=[] := counter
      rw [←counterEmpty,Function.update_eq_self,Function.update_eq_self,Function.update_eq_self,Function.update_eq_self]
    exact ⟨1,by simp,⟨1,store⟩,ran,halted,unchanged.symm⟩
  | succ count ih =>
    let consumed := Function.update store (w 14) (List.replicate count true)
    have consumedPorts : consumed (w 13)=List.replicate (consumed (w 13)).length true := by
      simpa [consumed,w.injective.eq_iff] using ports
    have consumedEmpty (i : Fin 15) (member : i∈([2,3,4,5,7,8,9,10,11,12] : List (Fin 15))) : consumed (w i)=[] := by
      have different : i≠14 := by intro eq;subst i;simp at member
      simpa [consumed,w.injective.eq_iff,different] using empty i member
    obtain ⟨bodyTime,bodyBound,bodyFinish,bodyRun,bodyHalt,bodyStore⟩ := emitRow_executes extra w consumed consumedPorts consumedEmpty
    let next := rowResult extra w consumed
    have nextCounter : next (w 14)=List.replicate count true := by simp [next,rowResult,consumed,w.injective.eq_iff]
    have nextPorts : next (w 13)=List.replicate (next (w 13)).length true := by
      simpa [next,rowResult,consumed,w.injective.eq_iff] using ports
    have nextBound : (next (w 0)).length+(next (w 1)).length+(next (w 13)).length+2*count ≤ limit := by
      simp only [next,rowResult,consumed,Function.update_apply,w.injective.eq_iff] at *
      simp only [Fin.reduceEq,ite_true,ite_false,List.length_cons] at *
      omega
    have nextEmpty (i : Fin 15) (member : i∈([2,3,4,5,7,8,9,10,11,12] : List (Fin 15))) : next (w i)=[] := by
      have a : i≠0 := by intro eq;subst i;simp at member
      have b : i≠1 := by intro eq;subst i;simp at member
      have c : i≠6 := by intro eq;subst i;simp at member
      simpa [next,rowResult,w.injective.eq_iff,a,b,c] using consumedEmpty i member
    obtain ⟨tailTime,tailBound,tailFinish,tailRun,tailHalt,tailStore⟩ := ih next nextCounter nextPorts nextBound nextEmpty
    have firstRun := repeat_iteration (w 14) (emitRow extra w) store true (List.replicate count true)
      (by simpa only [List.replicate_succ] using counter) bodyTime bodyFinish bodyRun bodyHalt
    change Machine.run (step (emitCompletion extra w).program) (bodyTime+2) ⟨0,store⟩=some ⟨0,bodyFinish.store⟩ at firstRun
    have bodyLimit : bodyTime ≤ 320*(limit+1)^3 := by
      apply bodyBound.trans
      apply (rowCost_le _ _ _).trans
      apply Nat.mul_le_mul_left
      apply Nat.pow_le_pow_left
      simp only [consumed,Function.update_of_ne (w.injective.ne (by decide : (0:Fin 15)≠14)),
        Function.update_of_ne (w.injective.ne (by decide : (1:Fin 15)≠14)),
        Function.update_of_ne (w.injective.ne (by decide : (13:Fin 15)≠14))]
      omega
    refine ⟨bodyTime+2+tailTime,?_,tailFinish,?_,tailHalt,?_⟩
    · nlinarith only [bodyLimit,tailBound]
    · rw [Machine.run_add,firstRun,Option.bind_some,bodyStore]
      exact tailRun
    · rw [tailStore]
      funext r
      by_cases c : r=w 14
      · subst r;simp [completionResult,w.injective.eq_iff]
      · by_cases a : r=w 0
        · subst r
          simp [completionResult,next,rowResult,consumed,w.injective.eq_iff,List.replicate_succ,replicate_append_cons]
        · by_cases b : r=w 1
          · subst r
            simp [completionResult,next,rowResult,consumed,w.injective.eq_iff,List.replicate_succ,replicate_append_cons]
          · by_cases o : r=w 6
            · subst r
              simp [completionResult,next,rowResult,consumed,w.injective.eq_iff,completionRows,sequence_append,
                List.reverse_append,List.append_assoc]
            · simp [completionResult,next,rowResult,consumed,c,a,b,o]

end Counting.External.MatchingMachine
