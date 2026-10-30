import Counting.ExternalCNFCodeBounds

namespace Counting.External.CNFMachine
open StackMachine StackMachine.Routine SATVerification
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 65536

def formulaRows (current width : Nat) : List (List (Nat×Bool)) → List (List (Nat×Bool))
  | [] => []
  | clause::rest => clauseRows current width clause++formulaRows (current+width+1) width rest

def generatorFormulaLoop (extra : Nat) (w : ClauseWorkspace extra) : Routine (extra+50) :=
  forEach (w 23) (generatorClause extra w)

def formulaResult (extra : Nat) (w : ClauseWorkspace extra) (store : Fin (extra+52) → List Bool)
    (width : Nat) (clauses : List (List (Nat×Bool))) (suffix : List Bool) :=
  Function.update (Function.update (Function.update (Function.update store (w 23) []) (w 0) suffix)
    (w 34) (List.replicate (clauses.length*(width+1)) true++store (w 34)))
    (w 42) ((Encoding.sequence (Encoding.list literalCodec) (formulaRows (store (w 34)).length width clauses)).reverse++store (w 42))

def formulaCodeLimit (sourceLimit indexLimit width : Nat) := 2*(sourceLimit+indexLimit+width+1)+2

theorem generatorFormulaLoop_executes (extra : Nat) (w : ClauseWorkspace extra)
    (clauses : List (List (Nat×Bool))) (width sourceLimit indexLimit : Nat)
    (store : Fin (extra+52) → List Bool) (accepted : Bool) (suffix tail : List Bool)
    (source : store (w 0)=Encoding.sequence (Encoding.list literalCodec) clauses++suffix)
    (sourceBound : (store (w 0)).length ≤ sourceLimit)
    (counter : store (w 23)=List.replicate clauses.length true)
    (status : store (w 1)=accepted::tail)
    (widthEq : store (w 47)=List.replicate width true)
    (indexBound : (store (w 34)).length+clauses.length*(width+1) ≤ indexLimit)
    (longEnough : ∀ clause∈clauses,clause.length ≤ width)
    (empty : ∀ i∈generatorClauseScratch,store (w i)=[]) :
    ∃ time  ≤  clauses.length*(50000*(sourceLimit+indexLimit+width+formulaCodeLimit sourceLimit indexLimit width+2)^3+2)+1,
      Executes (generatorFormulaLoop extra w) store time (formulaResult extra w store width clauses suffix) := by
  have ne (i j : Fin 52) (h : i≠j) : w i≠w j := fun same => h (w.injective same)
  induction clauses generalizing store with
  | nil =>
    have run := repeat_empty (w 23) (generatorClause extra w) store counter
    have unchanged : formulaResult extra w store width [] suffix=store := by
      have counterEmpty : store (w 23)=[] := counter
      have sourceEq : store (w 0)=suffix := source
      simp only [formulaResult,List.length_nil,Nat.zero_mul,List.replicate_zero,List.nil_append,
        formulaRows,Encoding.sequence,List.reverse_nil]
      rw [←counterEmpty,Function.update_eq_self,←sourceEq,Function.update_eq_self,
        Function.update_eq_self,Function.update_eq_self]
    exact ⟨1,by simp,⟨⟨1,store⟩,run.1,run.2,unchanged.symm⟩⟩
  | cons clause rest ih =>
    let consumed := Function.update store (w 23) (List.replicate rest.length true)
    let remaining := Encoding.sequence (Encoding.list literalCodec) rest++suffix
    have consumedSource : consumed (w 0)=(Encoding.list literalCodec).encode clause++remaining := by
      simpa [consumed,w.injective.eq_iff,Encoding.sequence,remaining,List.append_assoc] using source
    have consumedBound : (consumed (w 0)).length ≤ sourceLimit := by simpa [consumed,w.injective.eq_iff] using sourceBound
    have consumedCurrent : consumed (w 34)=store (w 34) := by simp [consumed,w.injective.eq_iff]
    have consumedEmpty (i : Fin 52) (member : i∈generatorClauseScratch) : consumed (w i)=[] := by
      have different : i≠23 := by intro equal;subst i;simp [generatorClauseScratch] at member
      simpa [consumed,w.injective.eq_iff,different] using empty i member
    have codes (j : Nat) (less : j<width) (i : Fin 6) :
        (literalCodec.encode (gateSource ((consumed (w 34)).length+j)
          ((clause.drop j).headD ((consumed (w 34)).length+width,true)) i)).length ≤ formulaCodeLimit sourceLimit indexLimit width := by
      apply gateCode_source_bound clause remaining (consumed (w 34)).length width (sourceLimit+indexLimit+width+1) ?_ ?_ j less i
      · rw [←consumedSource];omega
      · rw [consumedCurrent];simp only [List.length_cons] at indexBound;omega
    obtain ⟨bodyTime,bodyBound,finishBody,bodyRun,bodyHalt,bodyStore⟩ := generatorClause_executes extra w consumed width
      (formulaCodeLimit sourceLimit indexLimit width) clause accepted remaining tail consumedSource
      (by simp [consumed,w.injective.eq_iff,status]) (by simp [consumed,w.injective.eq_iff,widthEq])
      (longEnough clause (by simp)) consumedEmpty codes
    let next := clauseResult extra w consumed width clause remaining
    have nextSource : next (w 0)=Encoding.sequence (Encoding.list literalCodec) rest++suffix := by simp [next,clauseResult,w.injective.eq_iff,remaining]
    have nextBound : (next (w 0)).length ≤ sourceLimit := by
      rw [nextSource]
      rw [source] at sourceBound
      simp only [Encoding.sequence,List.length_append] at sourceBound
      simp only [List.length_append];omega
    have nextCounter : next (w 23)=List.replicate rest.length true := by simp [next,clauseResult,consumed,w.injective.eq_iff]
    have nextStatus : next (w 1)=accepted::tail := by simp [next,clauseResult,consumed,w.injective.eq_iff,status]
    have nextWidth : next (w 47)=List.replicate width true := by simp [next,clauseResult,consumed,w.injective.eq_iff,widthEq]
    have nextCurrent : next (w 34)=List.replicate (width+1) true++store (w 34) := by simp [next,clauseResult,consumed,w.injective.eq_iff]
    have nextIndex : (next (w 34)).length+rest.length*(width+1) ≤ indexLimit := by
      rw [nextCurrent];simp only [List.length_append,List.length_replicate,List.length_cons] at *
      nlinarith only [indexBound]
    have nextEmpty (i : Fin 52) (member : i∈generatorClauseScratch) : next (w i)=[] := by
      have a : i≠0 := by intro equal;subst i;simp [generatorClauseScratch] at member
      have b : i≠34 := by intro equal;subst i;simp [generatorClauseScratch] at member
      have c : i≠42 := by intro equal;subst i;simp [generatorClauseScratch] at member
      simpa [next,clauseResult,w.injective.eq_iff,a,b,c] using consumedEmpty i member
    obtain ⟨tailTime,tailBound,finishTail,tailRun,tailHalt,tailStore⟩ := ih next nextSource nextBound nextCounter nextStatus nextWidth
      nextIndex (fun other member=>longEnough other (by simp [member])) nextEmpty
    have firstRun := repeat_iteration (w 23) (generatorClause extra w) store true (List.replicate rest.length true)
      (by simpa only [List.length_cons,List.replicate_succ] using counter) bodyTime finishBody bodyRun bodyHalt
    change Machine.run (step (generatorFormulaLoop extra w).program) (bodyTime+2) ⟨0,store⟩=some ⟨0,finishBody.store⟩ at firstRun
    have bodyLimit : bodyTime ≤ 50000*(sourceLimit+indexLimit+width+formulaCodeLimit sourceLimit indexLimit width+2)^3 := by
      apply bodyBound.trans
      apply Nat.mul_le_mul_left
      apply Nat.pow_le_pow_left
      rw [consumedCurrent]
      simp only [List.length_cons] at indexBound
      omega
    refine ⟨bodyTime+2+tailTime,?_,⟨finishTail,?_,tailHalt,?_⟩⟩
    · simp only [List.length_cons];nlinarith only [bodyLimit,tailBound]
    · rw [Machine.run_add,firstRun,Option.bind_some,bodyStore]
      exact tailRun
    · rw [tailStore]
      funext r
      by_cases a : r=w 23
      · subst r;simp [formulaResult,w.injective.eq_iff]
      · by_cases b : r=w 0
        · subst r;simp [formulaResult,w.injective.eq_iff]
        · by_cases c : r=w 34
          · subst r
            simp only [formulaResult,Function.update_of_ne (ne 34 42 (by decide)),Function.update_self,nextCurrent,
              List.length_cons,←List.append_assoc,List.replicate_append_replicate]
            congr 2
            ring
          · by_cases d : r=w 42
            · subst r
              simp [formulaResult,next,clauseResult,consumed,w.injective.eq_iff,formulaRows,sequence_append,
                List.reverse_append,List.append_assoc,Nat.add_comm,Nat.add_left_comm,Nat.add_assoc]
            · simp [formulaResult,next,clauseResult,consumed,a,b,c,d]

end Counting.External.CNFMachine
