import Counting.ExternalSATLiteralRead
import Counting.StackBooleanFold
import Counting.StackCompare

namespace Counting.External.SATVerification
open StackMachine StackMachine.Routine StackMachine.EncodingPrograms
set_option backward.isDefEq.respectTransparency false

def satLookupRoles (extra : Nat) (w : SATWorkspace extra) : LookupWorkspace (extra+19) :=
  ⟨fun i => w (![18,17,26,28,19,1,3,4,5,6,9,10,11] i),by
    intro i j same
    have equal := w.injective same
    fin_cases i <;> fin_cases j <;> simp_all⟩

def literalVote (bits : List Bool) (literal : Nat×Bool) : Bool :=
  decide (bits[literal.1]?.toList=[literal.2])

def literalRoutine (extra : Nat) (w : SATWorkspace extra) : Routine (extra+30) :=
  sequence (readLiteral extra w)
    (sequence (boundedLookup (extra+19) (satLookupRoles extra w))
      (sequence (ofProgram (combineFlagsProgram (extra+30) (w 1)))
        (sequence (ofProgram (Compare.equalityProgram (extra+30) (w 19) (w 21) (w 22)))
          (sequence (BooleanFold.single .disjunction (w 22) (w 20)) (clear (w 18))))))

def literalScratch : List (Fin 32) := [2,3,4,5,6,9,10,11,18,19,21,22,26,28]

theorem literalRoutine_executes (extra : Nat) (w : SATWorkspace extra)
    (store : Fin (extra+32) → List Bool) (literal : Nat×Bool) (accepted value : Bool)
    (suffix tail valueTail : List Bool)
    (source : store (w 0)=(Encoding.product Encoding.natural Encoding.boolean).encode literal++suffix)
    (status : store (w 1)=accepted::tail) (clause : store (w 20)=value::valueTail)
    (empty : ∀ i∈literalScratch,store (w i)=[]) :
    ∃ time ≤ 200*((store (w 0)).length+(store (w 17)).length+1)^3,
      Executes (literalRoutine extra w) store time
        (Function.update (Function.update (Function.update store (w 0) suffix)
          (w 1) ((accepted && (store (w 17))[literal.1]?.isSome)::tail))
          (w 20) ((value || literalVote (store (w 17)) literal)::valueTail)) := by
  have ne (i j : Fin 32) (h : i≠j) : w i≠w j := fun same => h (w.injective same)
  let bits := store (w 17)
  let code := Encoding.natural.encode literal.1
  let found := bits[literal.1]?
  let read := Function.update (Function.update (Function.update store (w 0) suffix) (w 18) code) (w 21) [literal.2]
  have readEmpty (i : Fin 32) (member : i∈([2,3,4,5,6,9,10,18,21]:List (Fin 32))) : store (w i)=[] :=
    empty i (by simp only [literalScratch,List.mem_cons,List.not_mem_nil,or_false] at member ⊢;tauto)
  obtain ⟨readTime,readBound,reading⟩ := readLiteral_executes extra w store literal.1 literal.2 accepted suffix tail
    source status readEmpty
  let looked := Function.update (Function.update read (w 19) found.toList) (w 1) (found.isSome::accepted::tail)
  have lookupEmpty (i : Fin 13) (member : i∈([2,3,6,7,8,9,10,11,12]:List (Fin 13))) :
      read ((satLookupRoles extra w) i)=[] := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    all_goals simp [satLookupRoles,read,w.injective.eq_iff,empty,literalScratch]
  obtain ⟨lookupTime,lookupBound,lookupRun⟩ := boundedLookup_executes (extra+19) (satLookupRoles extra w) read literal.1
    (by simp [satLookupRoles,read,w.injective.eq_iff,code]) lookupEmpty
  have lookedRun : Executes (boundedLookup (extra+19) (satLookupRoles extra w)) read lookupTime looked := by
    simpa [satLookupRoles,read,looked,found,bits,w.injective.eq_iff,status,empty,literalScratch] using lookupRun
  let valid := Function.update looked (w 1) ((accepted && found.isSome)::tail)
  have combining := combineFlags_executes (extra+30) (w 1) looked accepted found.isSome tail
    (by simp [looked])
  let compared := Function.update (Function.update (Function.update valid (w 19) []) (w 21) [])
    (w 22) [literalVote bits literal]
  have compareRun : Executes (ofProgram (Compare.equalityProgram (extra+30) (w 19) (w 21) (w 22))) valid
      (Compare.equalityCost found.toList [literal.2]) compared := by
    simpa +instances [Compare.equalityProgram,valid,looked,read,w.injective.eq_iff,
      compared,found,literalVote,empty,literalScratch] using
      Compare.equality_executes (extra+30) (w 19) (w 21) (w 22) (ne 19 21 (by decide))
        (ne 19 22 (by decide)) (ne 21 22 (by decide)) valid
  have folding := BooleanFold.single_executes .disjunction (w 22) (w 20) (ne 22 20 (by decide)) compared
    (literalVote bits literal) value [] valueTail (by simp [compared])
    (by simp [compared,valid,looked,read,w.injective.eq_iff,clause])
  let folded := BooleanFold.updated (w 22) (w 20) compared [] (value || literalVote bits literal) valueTail
  have clearing := clear_executes (w 18) folded
  have headerSize : (folded (w 18)).length=code.length := by
    simp [folded,BooleanFold.updated,compared,valid,looked,read,w.injective.eq_iff]
  rw [headerSize] at clearing
  have restored : Function.update folded (w 18) []=
      Function.update (Function.update (Function.update store (w 0) suffix)
        (w 1) ((accepted && found.isSome)::tail))
        (w 20) ((value || literalVote bits literal)::valueTail) := by
    funext r
    by_cases a : r=w 18
    · subst r;simp [w.injective.eq_iff,empty,literalScratch]
    · by_cases b : r=w 19
      · subst r;simp [folded,BooleanFold.updated,compared,w.injective.eq_iff,empty,literalScratch]
      · by_cases c : r=w 21
        · subst r;simp [folded,BooleanFold.updated,compared,w.injective.eq_iff,empty,literalScratch]
        · by_cases d : r=w 22
          · subst r;simp [folded,BooleanFold.updated,w.injective.eq_iff,empty,literalScratch]
          · by_cases e : r=w 1
            · subst r;simp [folded,BooleanFold.updated,compared,valid,w.injective.eq_iff]
            · simp [folded,BooleanFold.updated,compared,valid,looked,read,Function.update_apply,a,b,c,d,e]
  rw [restored] at clearing
  have combined := reading.sequence (lookedRun.sequence (combining.sequence (compareRun.sequence (folding.sequence clearing))))
  refine ⟨readTime+1+(lookupTime+1+(3+1+(Compare.equalityCost found.toList [literal.2]+1+(3+1+(code.length+1))))),?_,combined⟩
  have compareBound := Compare.equalityCost_le found.toList [literal.2]
  have foundLength : found.toList.length≤1 := by cases found <;> simp
  have codeBound : code.length≤(store (w 0)).length := by
    rw [source]
    simp only [Encoding.product,Encoding.boolean,List.length_append,List.length_cons,List.length_nil]
    dsimp [code]
    omega
  have lookupBound' : lookupTime≤100*(bits.length+code.length+1)^3 := by
    simpa [satLookupRoles,read,w.injective.eq_iff,bits,code] using lookupBound
  have powered : (bits.length+code.length+1)^3 ≤ ((store (w 0)).length+bits.length+1)^3 :=
    Nat.pow_le_pow_left (by omega) 3
  have cubic : (store (w 0)).length+bits.length+1 ≤ ((store (w 0)).length+bits.length+1)^3 := Nat.le_self_pow (by decide) _
  have lookupBig := lookupBound'.trans (Nat.mul_le_mul_left 100 powered)
  simp only [List.length_cons,List.length_nil] at compareBound
  change _≤200*((store (w 0)).length+bits.length+1)^3
  omega

end Counting.External.SATVerification
