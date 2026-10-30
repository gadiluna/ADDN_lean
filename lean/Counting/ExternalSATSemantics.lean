import Counting.ExternalSATFormula

namespace Counting.External.SATVerification

theorem lookup_present_iff (bits : List Bool) (index : Nat) :
    bits[index]?.isSome=true ↔ index<bits.length := by simp

theorem vote_eq_of_present (bits : List Bool) (literal : Nat×Bool)
    (present : bits[literal.1]?.isSome=true) :
    literalVote bits literal=(bits[literal.1]?.getD false == literal.2) := by
  cases found : bits[literal.1]? with
  | none => simp [found] at present
  | some bit =>
    simp [literalVote,found]
    cases bit <;> cases literal.2 <;> rfl

theorem formulaValue_eq (bits : List Bool) (clauses : List (List (Nat×Bool)))
    (valid : formulaRange bits clauses=true) :
    formulaValue bits clauses=evalRaw ([],clauses) bits := by
  have present : ∀ clause∈clauses,∀ literal∈clause,bits[literal.1]?.isSome=true := by
    simpa only [formulaRange,clauseRange,List.all_eq_true] using valid
  apply Bool.eq_iff_iff.mpr
  simp only [formulaValue,clauseValue,evalRaw,List.all_eq_true,List.any_eq_true]
  constructor
  · intro all clause member
    obtain ⟨literal,inside,vote⟩ := all clause member
    exact ⟨literal,inside,(vote_eq_of_present bits literal (present clause member literal inside)) ▸ vote⟩
  · intro all clause member
    obtain ⟨literal,inside,vote⟩ := all clause member
    refine ⟨literal,inside,?_⟩
    rw [vote_eq_of_present bits literal (present clause member literal inside)]
    exact vote

def rawVoteCheck (raw : CNFEncoding.Raw) (bits : List Bool) : Bool :=
  raw.1.all id && decide (bits.length=raw.1.length) && formulaRange bits raw.2 && formulaValue bits raw.2

theorem rawVoteCheck_eq (raw : CNFEncoding.Raw) (bits : List Bool) : rawVoteCheck raw bits=checkRaw raw bits := by
  apply Bool.eq_iff_iff.mpr
  simp only [rawVoteCheck,checkRaw,validRaw,Bool.and_eq_true,decide_eq_true_eq]
  constructor
  · rintro ⟨⟨⟨markers,length⟩,range⟩,value⟩
    have indices : raw.2.all (fun clause => clause.all (fun literal => decide (literal.1<raw.1.length)))=true := by
      simpa only [formulaRange,clauseRange,List.all_eq_true,lookup_present_iff,length,decide_eq_true_eq] using range
    refine ⟨⟨⟨markers,indices⟩,length⟩,?_⟩
    rw [formulaValue_eq bits raw.2 range] at value
    exact value
  · rintro ⟨⟨⟨markers,indices⟩,length⟩,value⟩
    have range : formulaRange bits raw.2=true := by
      simpa only [formulaRange,clauseRange,List.all_eq_true,lookup_present_iff,length,decide_eq_true_eq] using indices
    refine ⟨⟨⟨markers,length⟩,range⟩,?_⟩
    rw [formulaValue_eq bits raw.2 range]
    exact value

end Counting.External.SATVerification
