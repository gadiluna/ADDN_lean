import Counting.ExternalGeneratorPrepareCost
import Counting.ExternalGeneratorCounts
import Counting.ExternalGeneratorBodyCost
import Counting.ExternalGeneratorHeaders

namespace Counting.External.CookLevin.StackGenerator
open StackMachine StackMachine.Routine Tableau InitialRows

/-- A single finite-control stack program for the actual CNF reduction. -/
def generatorRoutine (extra : Nat) (w : GeneratorWorkspace extra) (program : Machine.Program)
    (coefficient exponent witnessCoefficient witnessExponent : Nat) : Routine (extra+30) :=
  sequence (generatorPrepare extra w coefficient exponent witnessCoefficient witnessExponent)
    (sequence (generatorCounts extra w program)
      (sequence (formulaBodyRoutine extra w program) (formulaHeadersRoutine extra w)))

def generatorCost (program : Machine.Program) (input : List Bool)
    (coefficient exponent witnessCoefficient witnessExponent : Nat) :=
  let witness := Complexity.polynomial witnessCoefficient witnessExponent input.length
  let time := timeBound coefficient exponent input witness
  let width := MachineBridge.width (capacity input witness) time
  let cells := (time+1)*width
  generatorPrepareCost input coefficient exponent witnessCoefficient witnessExponent+1+
    (generatorCountsCost program cells width witness+1+
      (formulaBodyBound program time width witness+1+
        formulaHeadersBound (cells*Cellular.alphabet program) (formulaClauseCount program cells width witness)))

theorem generatorRoutine_executes (extra : Nat) (w : GeneratorWorkspace extra) (program : Machine.Program)
    (coefficient exponent witnessCoefficient witnessExponent : Nat) (store : Fin (extra+32) → List Bool)
    (empty : ∀ i : Fin 32, i ≠ 28 → store (w i)=[]) :
    ∃ transitions ≤ generatorCost program (store (w 28)) coefficient exponent witnessCoefficient witnessExponent,
      ∃ result, Executes (generatorRoutine extra w program coefficient exponent witnessCoefficient witnessExponent) store transitions result ∧
        result (w 5)=reduce program coefficient exponent witnessCoefficient witnessExponent (store (w 28)) := by
  let input := store (w 28)
  let witness := Complexity.polynomial witnessCoefficient witnessExponent input.length
  let time := timeBound coefficient exponent input witness
  let width := MachineBridge.width (capacity input witness) time
  let cells := (time+1)*width
  let initialSetup := setup input witness time
  let formula := Tableau.formula (T:=time) (Cellular.dynamics program (finRotate width))
    (initialSetup.constraints program) (Cellular.accept program)
  let prepared := generatorPrepared w store coefficient exponent witnessCoefficient witnessExponent
  let counted := Function.update (Function.update prepared (w 23)
    (List.replicate (formulaClauseCount program cells width witness) true))
      (w 22) (List.replicate (cells*Cellular.alphabet program) true)
  let emitted := Function.update (Function.update counted (w 26) []) (w 5)
    (Encoding.sequence clauseCodec (formula.map (List.map CNFEncoding.literalRaw)))
  have preparation := generatorPrepare_executes extra w coefficient exponent witnessCoefficient witnessExponent store empty
  have countRun : Executes (generatorCounts extra w program) prepared (generatorCountsCost program cells width witness) counted := by
    apply generatorCounts_executes extra w program cells width witness prepared
    · simp [prepared,generatorPrepared,cells,time,width,witness,input]
    · simp [prepared,generatorPrepared,w.injective.eq_iff,width,time,witness,input]
    · simp [prepared,generatorPrepared,generatorBounded,w.injective.eq_iff,witness,input]
    · intro i hi
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
      rcases hi with rfl|rfl|rfl|rfl|rfl|rfl
      all_goals
        simp [prepared,generatorPrepared,generatorBounded,w.injective.eq_iff]
        apply empty
        decide
  obtain ⟨bodyTime,bodyBound,bodyRun⟩ := formulaBodyRoutine_executes extra w program time initialSetup counted
    (by simp [counted,prepared,generatorPrepared,generatorBounded,w.injective.eq_iff,time,witness,input])
    (by simp [counted,prepared,generatorPrepared,w.injective.eq_iff,width,time,witness,input])
    (by simp [counted,prepared,generatorPrepared,w.injective.eq_iff,initialSetup,setup,time,witness,input])
    (by simp [counted,prepared,generatorPrepared,w.injective.eq_iff,initialSetup,setup,input])
    (by simp [counted,prepared,generatorPrepared,generatorBounded,w.injective.eq_iff,initialSetup,setup,witness,input])
    (by simp [counted,prepared,generatorPrepared,w.injective.eq_iff,cells,width,time,witness,input])
    (by
      intro i hi
      simp only [generatorScratch,List.mem_cons,List.not_mem_nil,or_false] at hi
      rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
      all_goals
        simp [counted,prepared,generatorPrepared,generatorBounded,w.injective.eq_iff]
        apply empty
        decide)
  have body : Executes (formulaBodyRoutine extra w program) counted bodyTime emitted := by
    simpa only [emitted,formula,counted,prepared,generatorPrepared,generatorBounded,
      Function.update_of_ne (show w 5 ≠ w 22 by simp [w.injective.eq_iff]),
      Function.update_of_ne (show w 5 ≠ w 23 by simp [w.injective.eq_iff]),
      Function.update_of_ne (show w 5 ≠ w 26 by simp [w.injective.eq_iff]),
      Function.update_of_ne (show w 5 ≠ w 3 by simp [w.injective.eq_iff]),
      Function.update_of_ne (show w 5 ≠ w 1 by simp [w.injective.eq_iff]),
      Function.update_of_ne (show w 5 ≠ w 2 by simp [w.injective.eq_iff]),
      Function.update_of_ne (show w 5 ≠ w 0 by simp [w.injective.eq_iff]),
      Function.update_of_ne (show w 5 ≠ w 29 by simp [w.injective.eq_iff]),
      Function.update_of_ne (show w 5 ≠ w 4 by simp [w.injective.eq_iff]),
      Function.update_of_ne (show w 5 ≠ w 25 by simp [w.injective.eq_iff]),empty 5 (by decide),List.append_nil] using bodyRun
  obtain ⟨headerTime,headerBound,headerRun⟩ := formulaHeadersRoutine_executes extra w (cells*Cellular.alphabet program)
    (formulaClauseCount program cells width witness) emitted
    (by simp [emitted,counted,w.injective.eq_iff])
    (by simp [emitted,counted,w.injective.eq_iff])
    (by simp [emitted,counted,prepared,generatorPrepared,generatorBounded,w.injective.eq_iff,empty 18 (by decide)])
    (by simp [emitted,counted,prepared,generatorPrepared,generatorBounded,w.injective.eq_iff,empty 19 (by decide)])
    (by simp [emitted,counted,prepared,generatorPrepared,generatorBounded,w.injective.eq_iff,empty 31 (by decide)])
  have combined := preparation.sequence (countRun.sequence (body.sequence headerRun))
  refine ⟨generatorPrepareCost input coefficient exponent witnessCoefficient witnessExponent+1+
    (generatorCountsCost program cells width witness+1+(bodyTime+1+headerTime)),?_,_,combined,?_⟩
  · change _ ≤ generatorCost program input coefficient exponent witnessCoefficient witnessExponent
    unfold generatorCost
    change _ ≤ generatorPrepareCost input coefficient exponent witnessCoefficient witnessExponent+1+
      (generatorCountsCost program cells width witness+1+(formulaBodyBound program time width witness+1+
        formulaHeadersBound (cells*Cellular.alphabet program) (formulaClauseCount program cells width witness)))
    change bodyTime≤formulaBodyBound program time width witness at bodyBound
    omega
  · simp only [Function.update_self,emitted]
    change (Encoding.list Encoding.boolean).encode (List.replicate (cells*Cellular.alphabet program) true)++
      Encoding.natural.encode (formulaClauseCount program cells width witness)++
      Encoding.sequence clauseCodec (formula.map (List.map CNFEncoding.literalRaw))=
      CNFEncoding.codec.encode ⟨cells*Cellular.alphabet program,formula⟩
    rw [formula_codec_header]
    have count : formula.length=formulaClauseCount program cells width witness :=
      formula_length_exact initialSetup program
    rw [count]

end Counting.External.CookLevin.StackGenerator
