import Counting.ExternalCNFThreeSATSerialization
import Counting.ExternalCookLevinMachine

namespace Counting.External.CNFMachine

/-- Three-SAT uses the canonical CNF codec with exactly three occurrences
per clause. Repeated literals and unused variables remain admissible. -/
def ThreeSATLanguage : Complexity.Language :=
  Complexity.encodedLanguage CNFEncoding.codec (fun input =>
    (∀ clause∈input.2,clause.length=3) ∧ input.2.Satisfiable)

def rejectFormula : CNFInput :=
  ⟨1,[[⟨0,true⟩,⟨0,true⟩,⟨0,true⟩],[⟨0,false⟩,⟨0,false⟩,⟨0,false⟩]]⟩

theorem rejectFormula_three : ∀ clause∈rejectFormula.2,clause.length=3 := by
  change ∀ clause∈([[⟨0,true⟩,⟨0,true⟩,⟨0,true⟩],[⟨0,false⟩,⟨0,false⟩,⟨0,false⟩]] : CNF 1),clause.length=3
  simp

theorem rejectFormula_unsatisfiable : ¬rejectFormula.2.Satisfiable := by
  rintro ⟨assignment,satisfied⟩
  change Fin 1 → Bool at assignment
  change CNF.eval ([[⟨0,true⟩,⟨0,true⟩,⟨0,true⟩],[⟨0,false⟩,⟨0,false⟩,⟨0,false⟩]] : CNF 1) assignment = true at satisfied
  cases equal : assignment 0 <;> simp [CNF.eval,Literal.eval,equal] at satisfied

def reducedInput (input : CNFInput) : CNFInput :=
  ⟨input.2.targetVariables,input.2.toThreeSAT.toCNF⟩

theorem reducedInput_three (input : CNFInput) : ∀ clause∈(reducedInput input).2,clause.length=3 := by
  change ∀ clause∈input.2.toThreeSAT.toCNF,clause.length=3
  intro clause member
  obtain ⟨index,_,rfl⟩ := List.mem_map.mp member
  simp

theorem reducedInput_satisfiable (input : CNFInput) :
    (reducedInput input).2.Satisfiable ↔ input.2.Satisfiable :=
  input.2.toThreeSAT.toCNF_satisfiable.trans input.2.toThreeSAT_yes_iff

/-- A total encoded reduction. Invalid encodings map to a fixed valid
unsatisfiable three-CNF. The machine realization is proved separately. -/
def reduceThreeSAT (input : List Bool) : List Bool :=
  match CNFEncoding.codec.decodeExact input with
  | none => CNFEncoding.codec.encode rejectFormula
  | some formula => CNFEncoding.codec.encode (reducedInput formula)

theorem reduceThreeSAT_encoded (formula : CNFInput) :
    reduceThreeSAT (CNFEncoding.codec.encode formula)=CNFEncoding.codec.encode (reducedInput formula) := by
  have decoded := (Encoding.Codec.decodeExact_iff CNFEncoding.codec _ formula).mpr rfl
  simp [reduceThreeSAT,decoded]

theorem reduceThreeSAT_yes_iff (input : List Bool) :
    reduceThreeSAT input∈ThreeSATLanguage ↔ input∈CookLevin.SAT := by
  cases decoded : CNFEncoding.codec.decodeExact input with
  | none =>
    have absent : ¬input∈CookLevin.SAT := by
      rintro ⟨formula,encoded,_⟩
      have present := (Encoding.Codec.decodeExact_iff CNFEncoding.codec input formula).mpr encoded
      rw [decoded] at present
      cases present
    have rejected : ¬CNFEncoding.codec.encode rejectFormula∈ThreeSATLanguage := by
      rw [ThreeSATLanguage,Complexity.encodedLanguage_iff]
      exact fun pair => rejectFormula_unsatisfiable pair.2
    simp [reduceThreeSAT,decoded,absent,rejected]
  | some formula =>
    have encoded := (Encoding.Codec.decodeExact_iff CNFEncoding.codec input formula).mp decoded
    rw [←encoded,reduceThreeSAT_encoded,ThreeSATLanguage,Complexity.encodedLanguage_iff]
    change ((∀ clause∈(reducedInput formula).2,clause.length=3) ∧ (reducedInput formula).2.Satisfiable) ↔
      CNFEncoding.codec.encode formula∈Complexity.encodedLanguage CNFEncoding.codec (fun input=>input.2.Satisfiable)
    rw [Complexity.encodedLanguage_iff,reducedInput_satisfiable]
    exact and_iff_right (reducedInput_three formula)

end Counting.External.CNFMachine
