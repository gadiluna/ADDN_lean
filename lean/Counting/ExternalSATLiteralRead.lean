import Counting.ExternalSATParser
import Counting.ExternalSATLookup
import Counting.StackRoutineLists
import Counting.StackEncodingParserRelabel

namespace Counting.External.SATVerification
open StackMachine StackMachine.Routine StackMachine.EncodingPrograms
set_option backward.isDefEq.respectTransparency false

abbrev SATWorkspace (extra : Nat) := Fin 32 ↪ Fin (extra+32)

def satParserRoles (extra : Nat) (w : SATWorkspace extra) : Fin 17 ↪ Fin (extra+32) :=
  ⟨fun i => w (Fin.castLE (by omega) i),by
    intro i j same
    exact Fin.ext (congrArg (fun q : Fin 32 => q.val) (w.injective same))⟩

def satLiteralParser (extra : Nat) (w : SATWorkspace extra) := literalParser.relabel (satParserRoles extra w)

def readLiteral (extra : Nat) (w : SATWorkspace extra) : Routine (extra+30) :=
  sequence (satLiteralParser extra w).routine
    (sequence (booleanItem (extra+30) (w 2) (w 1) (w 21))
      (ofProgram (ListPrograms.reverseProgram (extra+30) (w 2) (w 18))))

theorem readLiteral_executes (extra : Nat) (w : SATWorkspace extra)
    (store : Fin (extra+32) → List Bool) (index : Nat) (sign accepted : Bool) (suffix tail : List Bool)
    (source : store (w 0)=(Encoding.product Encoding.natural Encoding.boolean).encode (index,sign)++suffix)
    (status : store (w 1)=accepted::tail)
    (empty : ∀ i : Fin 32,i∈([2,3,4,5,6,9,10,18,21] : List (Fin 32)) → store (w i)=[]) :
    ∃ time ≤ 60*((store (w 0)).length+1),
      Executes (readLiteral extra w) store time
        (Function.update (Function.update (Function.update store (w 0) suffix)
          (w 18) (Encoding.natural.encode index)) (w 21) [sign]) := by
  have ne (i j : Fin 32) (h : i≠j) : w i≠w j := fun same => h (w.injective same)
  let code := Encoding.natural.encode index
  let parsed := Function.update (Function.update store (w 0) suffix) (w 2) (sign::code.reverse)
  have workEmpty (r : Fin (extra+32)) (member : r∈(satLiteralParser extra w).work) : store r=[] := by
    simp only [satLiteralParser,VerifiedParser.relabel,Finset.mem_map] at member
    obtain ⟨i,member,rfl⟩ := member
    have choices : i=3 ∨ i=5 ∨ i=6 ∨ i=9 := by
      simpa [literalParser,VerifiedParser.product,DagParser.natural,naturalParser,
        DagParser.boolean,booleanParser,DagParser.naturalRoles] using member
    rcases choices with rfl|rfl|rfl|rfl
    all_goals simpa [satParserRoles] using empty _ (by decide)
  obtain ⟨parseTime,parseBound,parsing⟩ := (satLiteralParser extra w).executes store accepted tail status workEmpty
  have sourceRole : (satParserRoles extra w) 0=w 0 := rfl
  have flagRole : (satParserRoles extra w) 1=w 1 := rfl
  have outputRole : (satParserRoles extra w) 2=w 2 := rfl
  have coefficientEq : (satLiteralParser extra w).coefficient=45 := rfl
  have exponentEq : (satLiteralParser extra w).exponent=1 := rfl
  rw [coefficientEq,exponentEq,Complexity.polynomial,pow_one,sourceRole] at parseBound
  have effect : (satLiteralParser extra w).effect (store (w 0))=
      ⟨suffix,code++[sign],true⟩ := by
    rw [source]
    exact literalParser.roundtrip (index,sign) suffix
  change Executes (satLiteralParser extra w).routine store parseTime
    (parseStore (w 0) (w 1) (w 2) store accepted tail ((satLiteralParser extra w).effect (store (w 0)))) at parsing
  rw [effect] at parsing
  have parsedStore : parseStore (w 0) (w 1) (w 2) store accepted tail ⟨suffix,code++[sign],true⟩=parsed := by
    funext r
    by_cases a : r=w 0
    · subst r; simp [parsed,parseStore,w.injective.eq_iff]
    · by_cases b : r=w 1
      · subst r; simp [parsed,parseStore,w.injective.eq_iff,status]
      · by_cases c : r=w 2
        · subst r; simp [parsed,parseStore,w.injective.eq_iff,empty 2 (by decide)]
        · simp [parsed,parseStore,a,b,c]
  change Executes (satLiteralParser extra w).routine store parseTime
    (parseStore (w 0) (w 1) (w 2) store accepted tail ⟨suffix,code++[sign],true⟩) at parsing
  rw [parsedStore] at parsing
  have signRun := booleanItem_executes (extra+30) (w 2) (w 1) (w 21)
    (ne 2 1 (by decide)) (ne 2 21 (by decide)) (ne 1 21 (by decide)) parsed accepted tail
    (by simp [parsed,w.injective.eq_iff,status])
  let signed := Function.update (Function.update parsed (w 2) code.reverse) (w 21) [sign]
  have signStore : parseStore (w 2) (w 1) (w 21) parsed accepted tail (booleanEffect (parsed (w 2)))=signed := by
    funext r
    by_cases a : r=w 2
    · subst r; simp [parsed,parseStore,signed,booleanEffect,w.injective.eq_iff]
    · by_cases b : r=w 1
      · subst r; simp [parsed,parseStore,signed,booleanEffect,w.injective.eq_iff,status]
      · by_cases c : r=w 21
        · subst r; simp [parsed,parseStore,signed,booleanEffect,w.injective.eq_iff,empty 21 (by decide)]
        · simp [parsed,parseStore,signed,Function.update_apply,a,b,c]
  rw [signStore] at signRun
  have parsedNonempty : (parsed (w 2)).isEmpty=false := by simp [parsed]
  rw [parsedNonempty] at signRun
  have reversing := reverse_executes (extra+30) (w 2) (w 18) (ne 2 18 (by decide)) signed
  let finished := Function.update (Function.update (Function.update store (w 0) suffix)
    (w 18) code) (w 21) [sign]
  have reverseStore : Function.update (Function.update signed (w 2) []) (w 18)
      ((signed (w 2)).reverse++signed (w 18))=finished := by
    funext r
    by_cases a : r=w 2
    · subst r; simp [signed,parsed,finished,w.injective.eq_iff,empty 2 (by decide)]
    · by_cases b : r=w 18
      · subst r; simp [signed,parsed,finished,w.injective.eq_iff,empty 18 (by decide)]
      · simp [signed,parsed,finished,Function.update_apply,a,b,w.injective.eq_iff]
  rw [reverseStore] at reversing
  have signedSize : (signed (w 2)).length=code.length := by simp [signed,w.injective.eq_iff]
  rw [signedSize] at reversing
  have combined := parsing.sequence (signRun.sequence reversing)
  refine ⟨parseTime+1+(2+1+(2*code.length+1)),?_,combined⟩
  have codeBound : code.length≤(store (w 0)).length := by
    rw [source]
    simp only [Encoding.product,Encoding.boolean,List.length_append,List.length_cons,List.length_nil]
    dsimp [code]
    omega
  omega

end Counting.External.SATVerification
