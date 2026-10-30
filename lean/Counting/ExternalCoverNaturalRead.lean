import Counting.ExternalMatchingLiteralRead

namespace Counting.External.CoverMachine
open StackMachine StackMachine.Routine StackMachine.EncodingPrograms SATVerification MatchingMachine
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 700000

def naturalParserAt (extra : Nat) (w : SATWorkspace extra) := DagParser.natural.relabel (satParserRoles extra w)
def readNatural (extra : Nat) (w : SATWorkspace extra) : Routine (extra+30) :=
  sequence (naturalParserAt extra w).routine
    (ofProgram (ListPrograms.reverseProgram (extra+30) (w 2) (w 18)))

theorem readNatural_executes (extra : Nat) (w : SATWorkspace extra)
    (store : Fin (extra+32) → List Bool) (index : Nat) (accepted : Bool) (suffix tail : List Bool)
    (source : store (w 0)=Encoding.natural.encode index++suffix)
    (status : store (w 1)=accepted::tail)
    (empty : ∀ i∈([2,3,5,6,9,18] : List (Fin 32)),store (w i)=[]) :
    ∃ time ≤ 60*((store (w 0)).length+1),
      Executes (readNatural extra w) store time
        (Function.update (Function.update store (w 0) suffix) (w 18) (Encoding.natural.encode index)) := by
  let code := Encoding.natural.encode index
  let parsed := Function.update (Function.update store (w 0) suffix) (w 2) code.reverse
  have workEmpty (r : Fin (extra+32)) (member : r∈(naturalParserAt extra w).work) : store r=[] := by
    simp only [naturalParserAt,VerifiedParser.relabel,Finset.mem_map] at member
    obtain ⟨i,member,rfl⟩ := member
    have choices : i=3 ∨ i=5 ∨ i=6 ∨ i=9 := by
      simpa [DagParser.natural,naturalParser,DagParser.naturalRoles] using member
    rcases choices with rfl|rfl|rfl|rfl
    all_goals simpa [satParserRoles] using empty _ (by decide)
  obtain ⟨parseTime,parseBound,parsing⟩ := (naturalParserAt extra w).executes store accepted tail status workEmpty
  have coefficientEq : (naturalParserAt extra w).coefficient=40 := rfl
  have exponentEq : (naturalParserAt extra w).exponent=1 := rfl
  rw [coefficientEq,exponentEq,Complexity.polynomial,pow_one] at parseBound
  have effect : (naturalParserAt extra w).effect (store (w 0))=⟨suffix,code,true⟩ := by
    rw [source]
    exact DagParser.natural.roundtrip index suffix
  change Executes (naturalParserAt extra w).routine store parseTime
    (parseStore (w 0) (w 1) (w 2) store accepted tail ((naturalParserAt extra w).effect (store (w 0)))) at parsing
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
  change parseTime ≤ 40*((store (w 0)).length+1) at parseBound
  omega

end Counting.External.CoverMachine
