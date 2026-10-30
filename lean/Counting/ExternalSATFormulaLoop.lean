import Counting.ExternalSATClause

namespace Counting.External.SATVerification
open StackMachine StackMachine.Routine
set_option backward.isDefEq.respectTransparency false

def formulaRange (bits : List Bool) (formula : List (List (Nat×Bool))) := formula.all (clauseRange bits)
def formulaValue (bits : List Bool) (formula : List (List (Nat×Bool))) := formula.all (clauseValue bits)

def formulaLoop (extra : Nat) (w : SATWorkspace extra) := forEach (w 23) (clauseRoutine extra w)

theorem formulaLoop_executes (extra : Nat) (w : SATWorkspace extra)
    (literals : List (List (Nat×Bool))) (bits suffix tail valueTail : List Bool) (limit : Nat)
    (store : Fin (extra+32) → List Bool) (accepted value : Bool)
    (source : store (w 0)=Encoding.sequence (Encoding.list (Encoding.product Encoding.natural Encoding.boolean)) literals++suffix)
    (sourceBound : (store (w 0)).length≤limit) (witness : store (w 17)=bits)
    (counter : store (w 23)=List.replicate literals.length true)
    (status : store (w 1)=accepted::tail) (clause : store (w 27)=value::valueTail)
    (empty : ∀ i∈clauseScratch,store (w i)=[]) :
    ∃ time ≤ literals.length*(2100*(limit+bits.length+1)^4+2)+1,
      Executes (formulaLoop extra w) store time
        (Function.update (Function.update (Function.update (Function.update store (w 23) []) (w 0) suffix)
          (w 1) ((accepted && formulaRange bits literals)::tail))
          (w 27) ((value && formulaValue bits literals)::valueTail)) := by
  have ne (i j : Fin 32) (h : i≠j) : w i≠w j := fun same => h (w.injective same)
  induction literals generalizing store accepted value with
  | nil =>
    have counterEmpty : store (w 23)=[] := counter
    have run := repeat_empty (w 23) (clauseRoutine extra w) store counterEmpty
    have unchanged : Function.update (Function.update (Function.update (Function.update store (w 23) []) (w 0) suffix)
        (w 1) ((accepted && formulaRange bits [])::tail)) (w 27) ((value && formulaValue bits [])::valueTail)=store := by
      simp only [formulaRange,formulaValue,List.all_nil,Bool.and_true]
      rw [←counterEmpty,Function.update_eq_self,←show store (w 0)=suffix from source,Function.update_eq_self,
        ←status,Function.update_eq_self,←clause,Function.update_eq_self]
    exact ⟨1,by simp,⟨⟨1,store⟩,run.1,run.2,unchanged.symm⟩⟩
  | cons literal rest ih =>
    let remaining := Encoding.sequence (Encoding.list (Encoding.product Encoding.natural Encoding.boolean)) rest++suffix
    let count := List.replicate rest.length true
    let consumed := Function.update store (w 23) count
    have consumedSource : consumed (w 0)=(Encoding.list (Encoding.product Encoding.natural Encoding.boolean)).encode literal++remaining := by
      simpa only [consumed,Function.update_of_ne (ne 0 23 (by decide)),Encoding.sequence,List.append_assoc,remaining] using source
    have consumedEmpty (i : Fin 32) (member : i∈clauseScratch) : consumed (w i)=[] := by
      have different : i≠23 := by intro same;subst i;simp [clauseScratch] at member
      simpa only [consumed,Function.update_of_ne (ne i 23 different)] using empty i member
    obtain ⟨bodyTime,bodyBound,finishBody,bodyRun,bodyHalt,bodyStore⟩ :=
      clauseRoutine_executes extra w literal bits remaining tail valueTail consumed accepted value consumedSource
        (by simp [consumed,w.injective.eq_iff,witness])
        (by simp [consumed,w.injective.eq_iff,status]) (by simp [consumed,w.injective.eq_iff,clause]) consumedEmpty
    have consumedWitness : consumed (w 17)=bits := by simp [consumed,w.injective.eq_iff,witness]
    
    let next := Function.update (Function.update (Function.update consumed (w 0) remaining)
      (w 1) ((accepted && clauseRange bits literal)::tail)) (w 27) ((value && clauseValue bits literal)::valueTail)
    have nextSource : next (w 0)=remaining := by simp [next,w.injective.eq_iff]
    have nextBound : (next (w 0)).length≤limit := by
      rw [nextSource]
      rw [source] at sourceBound
      simp only [Encoding.sequence,List.length_append] at sourceBound
      dsimp [remaining]
      simp only [List.length_append]
      omega
    have nextWitness : next (w 17)=bits := by simp [next,consumed,w.injective.eq_iff,witness]
    have nextCounter : next (w 23)=List.replicate rest.length true := by simp [next,consumed,count,w.injective.eq_iff]
    have nextStatus : next (w 1)=(accepted && clauseRange bits literal)::tail := by simp [next,w.injective.eq_iff]
    have nextClause : next (w 27)=(value && clauseValue bits literal)::valueTail := by simp [next]
    have nextEmpty (i : Fin 32) (member : i∈clauseScratch) : next (w i)=[] := by
      have a : i≠0 := by intro same;subst i;simp [clauseScratch] at member
      have b : i≠1 := by intro same;subst i;simp [clauseScratch] at member
      have c : i≠27 := by intro same;subst i;simp [clauseScratch] at member
      simpa only [next,Function.update_of_ne (ne i 27 c),Function.update_of_ne (ne i 1 b),
        Function.update_of_ne (ne i 0 a)] using consumedEmpty i member
    obtain ⟨tailTime,tailBound,finishTail,tailRun,tailHalt,tailStore⟩ := ih next
      (accepted && clauseRange bits literal) (value && clauseValue bits literal)
      nextSource nextBound nextWitness nextCounter nextStatus nextClause nextEmpty
    have firstRun := repeat_iteration (w 23) (clauseRoutine extra w) store true count
      (by simpa only [List.length_cons,List.replicate_succ,count] using counter)
      bodyTime finishBody bodyRun bodyHalt
    change Machine.run (step (formulaLoop extra w).program) (bodyTime+2) ⟨0,store⟩=
      some ⟨0,finishBody.store⟩ at firstRun
    have bodyLimit : bodyTime≤2100*(limit+bits.length+1)^4 := by
      apply bodyBound.trans
      apply Nat.mul_le_mul_left
      apply Nat.pow_le_pow_left
      have bound : (consumed (w 0)).length≤limit := by simpa only [consumed,Function.update_of_ne (ne 0 23 (by decide))] using sourceBound
      omega
    refine ⟨bodyTime+2+tailTime,?_,⟨finishTail,?_,tailHalt,?_⟩⟩
    · simp only [List.length_cons]
      nlinarith
    · rw [Machine.run_add,firstRun,Option.bind_some,bodyStore]
      exact tailRun
    · rw [tailStore]
      funext r
      by_cases a : r=w 23
      · subst r;simp [w.injective.eq_iff]
      · by_cases b : r=w 0
        · subst r;simp [w.injective.eq_iff]
        · by_cases c : r=w 1
          · subst r;simp [w.injective.eq_iff,formulaRange,Bool.and_assoc]
          · by_cases d : r=w 27
            · subst r;simp [formulaValue,Bool.and_assoc]
            · simp [next,consumed,a,b,c,d]

end Counting.External.SATVerification
