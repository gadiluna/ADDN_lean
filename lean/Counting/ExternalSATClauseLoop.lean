import Counting.ExternalSATLiteral

namespace Counting.External.SATVerification
open StackMachine StackMachine.Routine
set_option backward.isDefEq.respectTransparency false

def clauseRange (bits : List Bool) (clause : List (Nat×Bool)) := clause.all (fun literal => bits[literal.1]?.isSome)
def clauseValue (bits : List Bool) (clause : List (Nat×Bool)) := clause.any (literalVote bits)

def clauseLoop (extra : Nat) (w : SATWorkspace extra) := forEach (w 24) (literalRoutine extra w)

theorem clauseLoop_executes (extra : Nat) (w : SATWorkspace extra)
    (literals : List (Nat×Bool)) (bits suffix tail valueTail : List Bool) (limit : Nat)
    (store : Fin (extra+32) → List Bool) (accepted value : Bool)
    (source : store (w 0)=Encoding.sequence (Encoding.product Encoding.natural Encoding.boolean) literals++suffix)
    (sourceBound : (store (w 0)).length≤limit) (witness : store (w 17)=bits)
    (counter : store (w 24)=List.replicate literals.length true)
    (status : store (w 1)=accepted::tail) (clause : store (w 20)=value::valueTail)
    (empty : ∀ i∈literalScratch,store (w i)=[]) :
    ∃ time ≤ literals.length*(200*(limit+bits.length+1)^3+2)+1,
      Executes (clauseLoop extra w) store time
        (Function.update (Function.update (Function.update (Function.update store (w 24) []) (w 0) suffix)
          (w 1) ((accepted && clauseRange bits literals)::tail))
          (w 20) ((value || clauseValue bits literals)::valueTail)) := by
  have ne (i j : Fin 32) (h : i≠j) : w i≠w j := fun same => h (w.injective same)
  induction literals generalizing store accepted value with
  | nil =>
    have counterEmpty : store (w 24)=[] := counter
    have run := repeat_empty (w 24) (literalRoutine extra w) store counterEmpty
    have unchanged : Function.update (Function.update (Function.update (Function.update store (w 24) []) (w 0) suffix)
        (w 1) ((accepted && clauseRange bits [])::tail)) (w 20) ((value || clauseValue bits [])::valueTail)=store := by
      simp only [clauseRange,clauseValue,List.all_nil,List.any_nil,Bool.and_true,Bool.or_false]
      rw [←counterEmpty,Function.update_eq_self,←show store (w 0)=suffix from source,Function.update_eq_self,
        ←status,Function.update_eq_self,←clause,Function.update_eq_self]
    exact ⟨1,by simp,⟨⟨1,store⟩,run.1,run.2,unchanged.symm⟩⟩
  | cons literal rest ih =>
    let remaining := Encoding.sequence (Encoding.product Encoding.natural Encoding.boolean) rest++suffix
    let count := List.replicate rest.length true
    let consumed := Function.update store (w 24) count
    have consumedSource : consumed (w 0)=(Encoding.product Encoding.natural Encoding.boolean).encode literal++remaining := by
      simpa only [consumed,Function.update_of_ne (ne 0 24 (by decide)),Encoding.sequence,List.append_assoc,remaining] using source
    have consumedEmpty (i : Fin 32) (member : i∈literalScratch) : consumed (w i)=[] := by
      have different : i≠24 := by intro same;subst i;simp [literalScratch] at member
      simpa only [consumed,Function.update_of_ne (ne i 24 different)] using empty i member
    obtain ⟨bodyTime,bodyBound,finishBody,bodyRun,bodyHalt,bodyStore⟩ :=
      literalRoutine_executes extra w consumed literal accepted value remaining tail valueTail consumedSource
        (by simp [consumed,w.injective.eq_iff,status]) (by simp [consumed,w.injective.eq_iff,clause]) consumedEmpty
    have consumedWitness : consumed (w 17)=bits := by simp [consumed,w.injective.eq_iff,witness]
    rw [consumedWitness] at bodyStore bodyBound
    let next := Function.update (Function.update (Function.update consumed (w 0) remaining)
      (w 1) ((accepted && bits[literal.1]?.isSome)::tail)) (w 20) ((value || literalVote bits literal)::valueTail)
    have nextSource : next (w 0)=remaining := by simp [next,w.injective.eq_iff]
    have nextBound : (next (w 0)).length≤limit := by
      rw [nextSource]
      rw [source] at sourceBound
      simp only [Encoding.sequence,List.length_append] at sourceBound
      dsimp [remaining]
      simp only [List.length_append]
      omega
    have nextWitness : next (w 17)=bits := by simp [next,consumed,w.injective.eq_iff,witness]
    have nextCounter : next (w 24)=List.replicate rest.length true := by simp [next,consumed,count,w.injective.eq_iff]
    have nextStatus : next (w 1)=(accepted && bits[literal.1]?.isSome)::tail := by simp [next,w.injective.eq_iff]
    have nextClause : next (w 20)=(value || literalVote bits literal)::valueTail := by simp [next]
    have nextEmpty (i : Fin 32) (member : i∈literalScratch) : next (w i)=[] := by
      have a : i≠0 := by intro same;subst i;simp [literalScratch] at member
      have b : i≠1 := by intro same;subst i;simp [literalScratch] at member
      have c : i≠20 := by intro same;subst i;simp [literalScratch] at member
      simpa only [next,Function.update_of_ne (ne i 20 c),Function.update_of_ne (ne i 1 b),
        Function.update_of_ne (ne i 0 a)] using consumedEmpty i member
    obtain ⟨tailTime,tailBound,finishTail,tailRun,tailHalt,tailStore⟩ := ih next
      (accepted && bits[literal.1]?.isSome) (value || literalVote bits literal)
      nextSource nextBound nextWitness nextCounter nextStatus nextClause nextEmpty
    have firstRun := repeat_iteration (w 24) (literalRoutine extra w) store true count
      (by simpa only [List.length_cons,List.replicate_succ,count] using counter)
      bodyTime finishBody bodyRun bodyHalt
    change Machine.run (step (clauseLoop extra w).program) (bodyTime+2) ⟨0,store⟩=
      some ⟨0,finishBody.store⟩ at firstRun
    have bodyLimit : bodyTime≤200*(limit+bits.length+1)^3 := by
      apply bodyBound.trans
      apply Nat.mul_le_mul_left
      apply Nat.pow_le_pow_left
      have bound : (consumed (w 0)).length≤limit := by simpa only [consumed,Function.update_of_ne (ne 0 24 (by decide))] using sourceBound
      omega
    refine ⟨bodyTime+2+tailTime,?_,⟨finishTail,?_,tailHalt,?_⟩⟩
    · simp only [List.length_cons]
      nlinarith
    · rw [Machine.run_add,firstRun,Option.bind_some,bodyStore]
      exact tailRun
    · rw [tailStore]
      funext r
      by_cases a : r=w 24
      · subst r;simp [w.injective.eq_iff]
      · by_cases b : r=w 0
        · subst r;simp [w.injective.eq_iff]
        · by_cases c : r=w 1
          · subst r;simp [w.injective.eq_iff,clauseRange,Bool.and_assoc]
          · by_cases d : r=w 20
            · subst r;simp [clauseValue,Bool.or_assoc]
            · simp [next,consumed,a,b,c,d]

end Counting.External.SATVerification
