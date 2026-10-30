import Counting.ExternalCNFGenerator
import Counting.ExternalCNFValidateExact

namespace Counting.External.CNFMachine
open StackMachine StackMachine.Routine SATVerification
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 65536

def entryValidationPositions : Fin 32 ↪ Fin 52 := ⟨fun i=>if i=31 then 47 else i.castLE (by decide),by
  intro i j equal;fin_cases i <;> fin_cases j <;> simp_all⟩
def entryValidationRoles (extra : Nat) (w : ClauseWorkspace extra) : SATWorkspace (extra+20) := entryValidationPositions.trans w

def acceptedContinuation (extra : Nat) (w : ClauseWorkspace extra) : Routine (extra+50) :=
  sequence (pushBit (w 1) true)
    (sequence (ofProgram (ListPrograms.copyProgram (extra+49) (w 46) (w 0) (w 50))) (formulaGenerator extra w))

def rejectedContinuation (extra : Nat) (w : ClauseWorkspace extra) : Routine (extra+50) :=
  prepend (w 1) (CNFEncoding.codec.encode rejectFormula)

def entryRoutine (extra : Nat) (w : ClauseWorkspace extra) : Routine (extra+50) :=
  sequence (ofProgram (ListPrograms.copyProgram (extra+49) (w 0) (w 46) (w 50)))
    (sequence (pushBit (w 1) true)
      (sequence (validateRoutine (extra+20) (entryValidationRoles extra w))
        (StackMachine.EncodingPrograms.branchRoutine (w 1) (acceptedContinuation extra w) (rejectedContinuation extra w))))

def typedGeneratorCost (input : CNFInput) := formulaGeneratorCost (CNFEncoding.codec.encode input).length
  input.1 input.2.length input.2.width
  (Encoding.sequence (Encoding.list literalCodec) (formulaRows input.1 input.2.width (CNFEncoding.toRaw input).2)).length

theorem acceptedContinuation_executes (extra : Nat) (w : ClauseWorkspace extra)
    (store : Fin (extra+52) → List Bool) (input : CNFInput)
    (backup : store (w 46)=CNFEncoding.codec.encode input) (source : store (w 0)=[])
    (status : store (w 1)=[]) (population : store (w 17)=List.replicate input.1 true)
    (count : store (w 25)=List.replicate input.2.length true)
    (widthEq : store (w 47)=List.replicate input.2.width true)
    (empty : ∀ i∈generatorScratch,store (w i)=[]) :
    ∃ time ≤ typedGeneratorCost input+5*(CNFEncoding.codec.encode input).length+5,
      ∃ result, Executes (acceptedContinuation extra w) store time result ∧
        result (w 1)=CNFEncoding.codec.encode (reducedInput input) := by
  have pushing := pushBit_executes (w 1) true store
  rw [status] at pushing
  let flagged := Function.update store (w 1) [true]
  have copying := copy_executes (extra+49) (w 46) (w 0) (w 50)
    (by simp [w.injective.eq_iff]) (by simp [w.injective.eq_iff]) (by simp [w.injective.eq_iff]) flagged
    (by simp [flagged,w.injective.eq_iff,empty 50 (by simp [generatorScratch,formulaPrepareScratch])])
  have b : flagged (w 46)=CNFEncoding.codec.encode input := by simp [flagged,w.injective.eq_iff,backup]
  have s : flagged (w 0)=[] := by simp [flagged,w.injective.eq_iff,source]
  rw [b,s,List.append_nil] at copying
  let restored := Function.update flagged (w 0) (CNFEncoding.codec.encode input)
  have preparedEmpty (i : Fin 52) (member : i∈generatorScratch) : restored (w i)=[] := by
    have a : i≠0 := by intro equal;subst i;simp [generatorScratch,formulaPrepareScratch,generatorClauseScratch] at member
    have b : i≠1 := by intro equal;subst i;simp [generatorScratch,formulaPrepareScratch,generatorClauseScratch] at member
    simp [restored,flagged,w.injective.eq_iff,a,b,empty i member]
  obtain ⟨t,bound,result,running,output⟩ := formulaGenerator_executes extra w restored (CNFEncoding.toRaw input) (by simp only [restored,Function.update_self];rfl)
    (by simp [restored,flagged,w.injective.eq_iff])
    (by simp [restored,flagged,w.injective.eq_iff,CNFEncoding.toRaw,population])
    (by simp [restored,flagged,w.injective.eq_iff,CNFEncoding.toRaw,count])
    (by simp [restored,flagged,w.injective.eq_iff,CNFEncoding.toRaw,rawWidth_mapped,widthEq]) preparedEmpty
  have typedBound : t ≤ typedGeneratorCost input := by
    simpa [restored,typedGeneratorCost,CNFEncoding.toRaw,rawWidth_mapped] using bound
  have typedOutput : result (w 1)=CNFEncoding.codec.encode (reducedInput input) := by
    rw [output]
    change _=CNFEncoding.rawCodec.encode (CNFEncoding.toRaw (reducedInput input))
    rw [formulaRows_eq_reducedInput]
    simp only [CNFEncoding.toRaw,List.length_replicate,List.length_map,rawWidth_mapped,CNF.targetVariables]
  exact ⟨1+1+(5*(CNFEncoding.codec.encode input).length+2+1+t),by omega,result,
    pushing.sequence (copying.sequence running),typedOutput⟩

end Counting.External.CNFMachine
