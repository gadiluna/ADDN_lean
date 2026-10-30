import Counting.StackRealizabilityVistaTyped
import Counting.StackRealizabilityVistaSyntax
import Counting.StackReadBranch
import Counting.StackRoutineBasic

namespace Counting.StackMachine.VistaComplement
open Routine RealizabilityCall
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option maxHeartbeats 2400000

def typedGate : Routine 128 := branchRead 104 typedBody (skip 128)

theorem binaryVerifier_syntax (input witness : List Bool)
    (accepted : Encoding.binaryComplementVerifier input witness=true) : syntaxAccepted input witness=true := by
  cases first : Encoding.vistaInput.decodeExact input <;>
    cases second : Encoding.twoOrderWitness.decodeExact witness <;>
      simp_all [Encoding.binaryComplementVerifier,syntaxAccepted]

theorem typedGate_executes (data : Fin 30→List Bool) (accepted : Bool) (tail : List Bool)
    (status : data 4=(accepted && syntaxAccepted (data 8) (data 9))::tail)
    (empty : ∀i:Fin 30,i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=5 ∨ i=6 ∨ i=7 → data i=[]) :
    ∃time≤Complexity.polynomial (typedCoefficient+3) 25 ((data 8).length+(data 9).length),
      ∃result, Executes typedGate (file data) time (file result) ∧
        result 4=(accepted && Encoding.binaryComplementVerifier (data 8) (data 9))::tail := by
  let condition := accepted && syntaxAccepted (data 8) (data 9)
  change data 4=condition::tail at status
  by_cases positive : condition=true
  · have parts : accepted=true ∧ syntaxAccepted (data 8) (data 9)=true := by
      simpa only [condition,Bool.and_eq_true] using positive
    have parses : (Encoding.vistaInput.decodeExact (data 8)).isSome=true ∧
        (Encoding.twoOrderWitness.decodeExact (data 9)).isSome=true := by
      simpa only [syntaxAccepted,Bool.and_eq_true] using parts.2
    obtain ⟨⟨vista,ell⟩,inputDecoded⟩ := Option.isSome_iff_exists.mp parses.1
    obtain ⟨⟨⟨first,a⟩,⟨second,b⟩⟩,witnessDecoded⟩ := Option.isSome_iff_exists.mp parses.2
    have input : data 8=Encoding.vistaInput.encode (vista,ell) :=
      ((Encoding.vistaInput.decodeExact_iff _ _).mp inputDecoded).symm
    have witness : data 9=Encoding.twoOrderWitness.encode ((first,a),(second,b)) :=
      ((Encoding.twoOrderWitness.decodeExact_iff _ _).mp witnessDecoded).symm
    obtain ⟨time,bound,result,run,output⟩ := typedBody_executes data vista ell first second a b true tail
      (by simpa only [positive] using status) input witness empty
    have selected : Executes (if condition then typedBody else skip 128) (file data) time (file result) := by
      simpa only [positive,↓reduceIte] using run
    have branched := branchRead_executes (104:Fin 130) typedBody (skip 128) condition tail
      (file data) (file result) time (by simpa [file] using status) selected
    refine ⟨time+3,?_,result,branched,?_⟩
    · have one : 1≤((data 8).length+(data 9).length+1)^25 := Nat.one_le_pow _ _ (by omega)
      simp only [Complexity.polynomial,Nat.add_mul] at bound ⊢
      omega
    · simpa only [Encoding.binaryComplementVerifier,inputDecoded,witnessDecoded,parts.1,Bool.true_and] using output
  · have negative : condition=false := Bool.eq_false_of_not_eq_true positive
    have noAnswer : (accepted && Encoding.binaryComplementVerifier (data 8) (data 9))=false := by
      apply Bool.eq_false_of_not_eq_true
      intro yes
      have parts : accepted=true ∧ Encoding.binaryComplementVerifier (data 8) (data 9)=true := by
        simpa only [Bool.and_eq_true] using yes
      have syntactic := binaryVerifier_syntax (data 8) (data 9) parts.2
      exact positive (by simp [condition,parts.1,syntactic])
    have selected : Executes (if condition then typedBody else skip 128) (file data) 0 (file data) := by
      simpa only [negative,Bool.false_eq_true,↓reduceIte] using skip_executes (file data)
    have branched := branchRead_executes (104:Fin 130) typedBody (skip 128) condition tail
      (file data) (file data) 0 (by simpa [file] using status) selected
    refine ⟨3,?_,data,branched,?_⟩
    · have one : 1≤((data 8).length+(data 9).length+1)^25 := Nat.one_le_pow _ _ (by omega)
      simp only [Complexity.polynomial,Nat.add_mul]
      omega
    · simpa only [negative,noAnswer] using status

end Counting.StackMachine.VistaComplement
