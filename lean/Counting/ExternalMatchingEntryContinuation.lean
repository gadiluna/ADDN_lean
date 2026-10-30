import Counting.ExternalMatchingGeneratedSize
import Counting.ExternalMatchingReduction
import Counting.ExternalMatchingValidation

namespace Counting.External.MatchingMachine
open StackMachine StackMachine.Routine SATVerification
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
set_option maxRecDepth 65536

def entryValidationPositions : Fin 32 ↪ Fin 64 :=
  ⟨fun i => i.castLE (by decide),by intro i j same;exact Fin.ext (congrArg (fun x : Fin 64 => x.val) same)⟩

def entryValidationRoles (extra : Nat) (w : GeneratorWorkspace extra) : SATWorkspace (extra+32) :=
  entryValidationPositions.trans w

def acceptedContinuation (extra : Nat) (w : GeneratorWorkspace extra) : Routine (extra+62) :=
  sequence (pushBit (w 1) true)
    (sequence (ofProgram (ListPrograms.copyProgram (extra+61) (w 51) (w 0) (w 63))) (matchingGenerator extra w))

def rejectedContinuation (extra : Nat) (w : GeneratorWorkspace extra) : Routine (extra+62) :=
  prepend (w 1) (ThreeDMEncoding.codec.encode rejectMatching)

def entryRoutine (extra : Nat) (w : GeneratorWorkspace extra) : Routine (extra+62) :=
  sequence (ofProgram (ListPrograms.copyProgram (extra+61) (w 0) (w 51) (w 63)))
    (sequence (pushBit (w 1) true)
      (sequence (MatchingValidation.routine (extra+32) (entryValidationRoles extra w))
        (StackMachine.EncodingPrograms.branchRoutine (w 1) (acceptedContinuation extra w) (rejectedContinuation extra w))))

def typedGeneratorCost (input : CNFInput) := matchingGeneratorCost (CNFEncoding.codec.encode input).length
  input.1 input.2.length
  (Encoding.sequence (Encoding.list Encoding.natural) (matchingRows input.1 (CNFEncoding.toRaw input).2)).length

theorem acceptedContinuation_executes (extra : Nat) (w : GeneratorWorkspace extra)
    (store : Fin (extra+64) → List Bool) (input : CNFInput)
    (three : ∀ clause ∈ input.2,clause.length=3)
    (backup : store (w 51)=CNFEncoding.codec.encode input) (source : store (w 0)=[])
    (status : store (w 1)=[]) (population : store (w 17)=List.replicate input.1 true)
    (count : store (w 25)=List.replicate input.2.length true)
    (empty : ∀ i∈generatorScratch,store (w i)=[]) :
    ∃ time ≤ typedGeneratorCost input+5*(CNFEncoding.codec.encode input).length+5,
      ∃ result,Executes (acceptedContinuation extra w) store time result ∧
        result (w 1)=ThreeDMEncoding.codec.encode (CNFMachine.asThreeSAT input three).sparseInput := by
  have pushing := pushBit_executes (w 1) true store
  rw [status] at pushing
  let flagged := Function.update store (w 1) [true]
  have copying := copy_executes (extra+61) (w 51) (w 0) (w 63)
    (by simp [w.injective.eq_iff]) (by simp [w.injective.eq_iff]) (by simp [w.injective.eq_iff]) flagged
    (by simp [flagged,w.injective.eq_iff,empty 63 (by simp [generatorScratch])])
  have b : flagged (w 51)=CNFEncoding.codec.encode input := by simp [flagged,w.injective.eq_iff,backup]
  have s : flagged (w 0)=[] := by simp [flagged,w.injective.eq_iff,source]
  rw [b,s,List.append_nil] at copying
  let restored := Function.update flagged (w 0) (CNFEncoding.codec.encode input)
  have preparedEmpty (i : Fin 64) (member : i∈generatorScratch) : restored (w i)=[] := by
    have a : i≠0 := by intro equal;subst i;simp [generatorScratch] at member
    have b : i≠1 := by intro equal;subst i;simp [generatorScratch] at member
    simp [restored,flagged,w.injective.eq_iff,a,b,empty i member]
  have rawThree : ∀ clause∈(CNFEncoding.toRaw input).2,clause.length=3 := by
    simpa [CNFEncoding.toRaw] using three
  have fits : ∀ clause∈(CNFEncoding.toRaw input).2,∀ literal∈clause,literal.1≤(CNFEncoding.toRaw input).1.length := by
    intro clause clauseMember literal literalMember
    obtain ⟨original,_member,rfl⟩ := List.mem_map.mp clauseMember
    obtain ⟨value,_inside,rfl⟩ := List.mem_map.mp literalMember
    simpa only [CNFEncoding.toRaw,List.length_replicate,CNFEncoding.literalRaw] using value.var.isLt.le
  obtain ⟨time,bound,result,running,output⟩ := matchingGenerator_executes extra w restored (CNFEncoding.toRaw input)
    (by simp only [restored,Function.update_self];rfl)
    (by simp [restored,flagged,w.injective.eq_iff])
    (by simp [restored,flagged,w.injective.eq_iff,CNFEncoding.toRaw,population])
    (by simp [restored,flagged,w.injective.eq_iff,CNFEncoding.toRaw,count]) rawThree fits preparedEmpty
  have typedBound : time ≤ typedGeneratorCost input := by
    simpa [restored,typedGeneratorCost,CNFEncoding.toRaw] using bound
  have typedOutput : result (w 1)=ThreeDMEncoding.codec.encode (CNFMachine.asThreeSAT input three).sparseInput := by
    rw [output]
    simpa only [CNFEncoding.toRaw,List.length_replicate,List.length_map] using matchingGenerator_output_eq input three
  exact ⟨1+1+(5*(CNFEncoding.codec.encode input).length+2+1+time),by omega,result,
    pushing.sequence (copying.sequence running),typedOutput⟩

end Counting.External.MatchingMachine
