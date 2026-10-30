import Counting.ExternalMatchingLiteralRead
import Counting.ExternalMatchingParser

namespace Counting.External.CoverNormalization
open StackMachine StackMachine.Routine StackMachine.EncodingPrograms SATVerification MatchingMachine
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 700000

def rowParserAt (extra : Nat) (w : SATWorkspace extra) := MatchingVerification.clauseParser.relabel (satParserRoles extra w)
def readRow (extra : Nat) (w : SATWorkspace extra) : Routine (extra+30) :=
  sequence (rowParserAt extra w).routine
    (ofProgram (ListPrograms.reverseProgram (extra+30) (w 2) (w 18)))

theorem readRow_executes (extra : Nat) (w : SATWorkspace extra)
    (store : Fin (extra+32) → List Bool) (row : MatchingVerification.RawClause) (accepted : Bool) (suffix tail : List Bool)
    (source : store (w 0)=MatchingVerification.clauseCodec.encode row++suffix)
    (status : store (w 1)=accepted::tail)
    (empty : ∀ i∈([2,3,5,6,9,18] : List (Fin 32)),store (w i)=[]) :
    ∃ time ≤ 160*((store (w 0)).length+1),
      Executes (readRow extra w) store time
        (Function.update (Function.update store (w 0) suffix) (w 18) (MatchingVerification.clauseCodec.encode row)) := by
  let code := MatchingVerification.clauseCodec.encode row
  let parsed := Function.update (Function.update store (w 0) suffix) (w 2) code.reverse
  have workEmpty (r : Fin (extra+32)) (member : r∈(rowParserAt extra w).work) : store r=[] := by
    simp only [rowParserAt,VerifiedParser.relabel,Finset.mem_map] at member
    obtain ⟨i,member,rfl⟩ := member
    have choices : i=3 ∨ i=5 ∨ i=6 ∨ i=9 := by
      exact (show ∀ j : Fin 17,j∈MatchingVerification.clauseParser.work → j=3 ∨ j=5 ∨ j=6 ∨ j=9 by decide) i member
    rcases choices with rfl|rfl|rfl|rfl
    all_goals simpa [satParserRoles] using empty _ (by decide)
  obtain ⟨parseTime,parseBound,parsing⟩ := (rowParserAt extra w).executes store accepted tail status workEmpty
  have coefficientEq : (rowParserAt extra w).coefficient=147 := rfl
  have exponentEq : (rowParserAt extra w).exponent=1 := rfl
  rw [coefficientEq,exponentEq,Complexity.polynomial,pow_one] at parseBound
  have effect : (rowParserAt extra w).effect (store (w 0))=⟨suffix,code,true⟩ := by
    rw [source]
    exact MatchingVerification.clauseParser.roundtrip row suffix
  change Executes (rowParserAt extra w).routine store parseTime
    (parseStore (w 0) (w 1) (w 2) store accepted tail ((rowParserAt extra w).effect (store (w 0)))) at parsing
  rw [effect] at parsing
  have parsedStore : parseStore (w 0) (w 1) (w 2) store accepted tail ⟨suffix,code,true⟩=parsed := by
    funext r
    by_cases a : r=w 0
    · subst r;simp [parsed,parseStore,w.injective.eq_iff]
    · by_cases b : r=w 1
      · subst r;simp [parsed,parseStore,w.injective.eq_iff,status]
      · by_cases c : r=w 2
        · subst r;simp [parsed,parseStore,w.injective.eq_iff,empty 2 (by decide)]
        · simp [parsed,parseStore,a,b,c]
  rw [parsedStore] at parsing
  have reversing := reverse_executes (extra+30) (w 2) (w 18) (by simp [w.injective.eq_iff]) parsed
  have final : Function.update (Function.update parsed (w 2) []) (w 18)
      ((parsed (w 2)).reverse++parsed (w 18))=
      Function.update (Function.update store (w 0) suffix) (w 18) code := by
    funext r
    by_cases a : r=w 2
    · subst r;simp [parsed,w.injective.eq_iff,empty 2 (by decide)]
    · by_cases b : r=w 18
      · subst r;simp [parsed,w.injective.eq_iff,empty 18 (by decide)]
      · simp [parsed,Function.update_apply,a,b]
  rw [final] at reversing
  have lengthEq : (parsed (w 2)).length=code.length := by simp [parsed]
  rw [lengthEq] at reversing
  refine ⟨parseTime+1+(2*code.length+1),?_,parsing.sequence reversing⟩
  have bound : code.length≤(store (w 0)).length := by rw [source];dsimp only [code];simp only [List.length_append];omega
  change parseTime ≤ 147*((store (w 0)).length+1) at parseBound
  omega

end Counting.External.CoverNormalization
