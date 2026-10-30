import Counting.ExternalCoverGeneratedSize
import Counting.ExternalCoverReduction

namespace Counting.External.CoverMachine
open StackMachine StackMachine.Routine SATVerification MatchingMachine
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
set_option maxRecDepth 65536

def acceptedContinuation (extra : Nat) (w : GeneratorWorkspace extra) : Routine (extra+62) :=
  sequence (pushBit (w 1) true)
    (sequence (ofProgram (ListPrograms.copyProgram (extra+61) (w 51) (w 0) (w 63))) (coverGenerator extra w))

def rejectedContinuation (extra : Nat) (w : GeneratorWorkspace extra) : Routine (extra+62) :=
  prepend (w 1) (X3CEncoding.codec.encode rejectCover)

def typedGeneratorCost (input : ThreeDMEncoding.Input) := coverGeneratorCost (ThreeDMEncoding.codec.encode input).length
  input.1 input.2.1
  (Encoding.sequence (Encoding.list Encoding.natural) (shiftedRows input.1 (ThreeDMEncoding.toRaw input).2)).length

theorem acceptedContinuation_executes (extra : Nat) (w : GeneratorWorkspace extra)
    (store : Fin (extra+64) → List Bool) (input : ThreeDMEncoding.Input)
    (backup : store (w 51)=ThreeDMEncoding.codec.encode input) (source : store (w 0)=[])
    (status : store (w 1)=[]) (population : store (w 17)=List.replicate input.1 true)
    (count : store (w 25)=List.replicate input.2.1 true)
    (empty : ∀ i∈generatorScratch,store (w i)=[]) :
    ∃ time ≤ typedGeneratorCost input+5*(ThreeDMEncoding.codec.encode input).length+5,
      ∃ result,Executes (acceptedContinuation extra w) store time result ∧
        result (w 1)=X3CEncoding.codec.encode (ThreeDMEncoding.coverInput input) := by
  have pushing := pushBit_executes (w 1) true store
  rw [status] at pushing
  let flagged := Function.update store (w 1) [true]
  have copying := copy_executes (extra+61) (w 51) (w 0) (w 63)
    (by simp [w.injective.eq_iff]) (by simp [w.injective.eq_iff]) (by simp [w.injective.eq_iff]) flagged
    (by simp [flagged,w.injective.eq_iff,empty 63 (by simp [generatorScratch])])
  have b : flagged (w 51)=ThreeDMEncoding.codec.encode input := by simp [flagged,w.injective.eq_iff,backup]
  have s : flagged (w 0)=[] := by simp [flagged,w.injective.eq_iff,source]
  rw [b,s,List.append_nil] at copying
  let restored := Function.update flagged (w 0) (ThreeDMEncoding.codec.encode input)
  have preparedEmpty (i : Fin 64) (member : i∈generatorScratch) : restored (w i)=[] := by
    have a : i≠0 := by intro equal;subst i;simp [generatorScratch] at member
    have b : i≠1 := by intro equal;subst i;simp [generatorScratch] at member
    simp [restored,flagged,w.injective.eq_iff,a,b,empty i member]
  have rawThree : ∀ row∈(ThreeDMEncoding.toRaw input).2,row.length=3 := by
    intro row member
    obtain ⟨triple,_member,rfl⟩ := List.mem_map.mp member
    exact ThreeDMEncoding.tripleRaw_length triple
  have fits : ∀ row∈(ThreeDMEncoding.toRaw input).2,∀ index∈row,index≤(ThreeDMEncoding.toRaw input).1.length := by
    intro row rowMember index indexMember
    obtain ⟨triple,_member,rfl⟩ := List.mem_map.mp rowMember
    rw [tripleRaw_eq] at indexMember
    simp only [List.mem_cons,List.not_mem_nil] at indexMember
    rcases indexMember with rfl|rfl|rfl|h
    all_goals first | contradiction | simpa only [ThreeDMEncoding.toRaw,List.length_replicate] using (triple _).isLt.le
  obtain ⟨time,bound,result,running,output⟩ := coverGenerator_executes extra w restored (ThreeDMEncoding.toRaw input)
    (by simp only [restored,Function.update_self];rfl)
    (by simp [restored,flagged,w.injective.eq_iff])
    (by simp [restored,flagged,w.injective.eq_iff,ThreeDMEncoding.toRaw,population])
    (by simp [restored,flagged,w.injective.eq_iff,ThreeDMEncoding.toRaw,count]) rawThree fits preparedEmpty
  have typedBound : time ≤ typedGeneratorCost input := by
    simpa [restored,typedGeneratorCost,ThreeDMEncoding.toRaw] using bound
  have typedOutput : result (w 1)=X3CEncoding.codec.encode (ThreeDMEncoding.coverInput input) := by
    rw [output]
    simpa only [ThreeDMEncoding.toRaw,List.length_replicate,List.length_map,ThreeDMEncoding.inputTriples_length] using coverGenerator_output_eq input
  exact ⟨1+1+(5*(ThreeDMEncoding.codec.encode input).length+2+1+time),by omega,result,
    pushing.sequence (copying.sequence running),typedOutput⟩

end Counting.External.CoverMachine
