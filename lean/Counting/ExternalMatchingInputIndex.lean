import Counting.ExternalCoverNaturalRead
import Counting.ExternalSATLiteral

namespace Counting.External.MatchingInputValidation
open StackMachine StackMachine.Routine StackMachine.EncodingPrograms SATVerification
set_option backward.isDefEq.respectTransparency false

def indexScratch : List (Fin 32) := [2,3,4,5,6,9,10,11,18,19,26,28]

/-- Bounded lookup validates a binary coordinate without expanding an
out-of-range number into an unbounded unary counter. -/
def indexGuard (extra : Nat) (w : SATWorkspace extra) : Routine (extra+30) :=
  sequence (CoverMachine.readNatural extra w)
    (sequence (boundedLookup (extra+19) (satLookupRoles extra w))
      (sequence (ofProgram (combineFlagsProgram (extra+30) (w 1)))
        (sequence (clear (w 19)) (clear (w 18)))))

theorem indexGuard_executes (extra : Nat) (w : SATWorkspace extra)
    (store : Fin (extra+32) → List Bool) (index : Nat) (accepted : Bool)
    (suffix tail : List Bool)
    (source : store (w 0)=Encoding.natural.encode index++suffix)
    (status : store (w 1)=accepted::tail)
    (empty : ∀ i∈indexScratch,store (w i)=[]) :
    ∃ time ≤ 200*((store (w 0)).length+(store (w 17)).length+1)^3,
      Executes (indexGuard extra w) store time
        (Function.update (Function.update store (w 0) suffix)
          (w 1) ((accepted && decide (index < (store (w 17)).length))::tail)) := by
  let bits:=store (w 17)
  let code:=Encoding.natural.encode index
  let found:=bits[index]?
  let read:=Function.update (Function.update store (w 0) suffix) (w 18) code
  have readEmpty (i : Fin 32) (member : i∈([2,3,5,6,9,18]:List (Fin 32))) : store (w i)=[] :=
    empty i (by simp only [indexScratch,List.mem_cons,List.not_mem_nil,or_false] at member ⊢;tauto)
  obtain ⟨readTime,readBound,reading⟩:=CoverMachine.readNatural_executes extra w store index accepted
    suffix tail source status readEmpty
  let looked:=Function.update (Function.update read (w 19) found.toList) (w 1) (found.isSome::accepted::tail)
  have lookupEmpty (i : Fin 13) (member : i∈([2,3,6,7,8,9,10,11,12]:List (Fin 13))) :
      read ((satLookupRoles extra w) i)=[] := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    all_goals simp [satLookupRoles,read,w.injective.eq_iff,empty,indexScratch]
  obtain ⟨lookupTime,lookupBound,lookupRun⟩:=boundedLookup_executes (extra+19) (satLookupRoles extra w) read index
    (by simp [satLookupRoles,read,code]) lookupEmpty
  have lookedRun : Executes (boundedLookup (extra+19) (satLookupRoles extra w)) read lookupTime looked := by
    simpa [satLookupRoles,read,looked,found,bits,w.injective.eq_iff,status,empty,indexScratch] using lookupRun
  let checked:=Function.update looked (w 1) ((accepted && found.isSome)::tail)
  have combine:=combineFlags_executes (extra+30) (w 1) looked accepted found.isSome tail (by simp [looked])
  have clearValue:=clear_executes (w 19) checked
  have valueAt : checked (w 19)=found.toList := by simp [checked,looked,w.injective.eq_iff]
  rw [valueAt] at clearValue
  let cleared:=Function.update checked (w 19) []
  have clearIndex:=clear_executes (w 18) cleared
  have headerAt : cleared (w 18)=code := by simp [cleared,checked,looked,read,w.injective.eq_iff]
  rw [headerAt] at clearIndex
  have flag : found.isSome=decide (index < bits.length) := by
    apply Bool.eq_iff_iff.mpr
    simp [found]
  have final : Function.update cleared (w 18) []=
      Function.update (Function.update store (w 0) suffix)
        (w 1) ((accepted && decide (index < bits.length))::tail) := by
    rw [←flag]
    funext r
    by_cases a : r=w 18
    · subst r;simp [w.injective.eq_iff,empty,indexScratch]
    · by_cases b : r=w 19
      · subst r;simp [cleared,w.injective.eq_iff,empty,indexScratch]
      · by_cases c : r=w 1
        · subst r;simp [cleared,checked,w.injective.eq_iff]
        · simp [cleared,checked,looked,read,a,b,c]
  rw [final] at clearIndex
  have executed:=reading.sequence (lookedRun.sequence (combine.sequence (clearValue.sequence clearIndex)))
  refine ⟨readTime+1+(lookupTime+1+(3+1+(found.toList.length+1+1+(code.length+1)))),?_,executed⟩
  have valueBound : found.toList.length ≤ 1 := by cases found <;> simp
  have codeBound : code.length ≤ (store (w 0)).length := by rw [source];dsimp [code];simp only [List.length_append];omega
  have lookupLimit : lookupTime ≤ 100*(bits.length+code.length+1)^3 := by
    simpa [satLookupRoles,read,w.injective.eq_iff,bits,code] using lookupBound
  have power : (bits.length+code.length+1)^3 ≤ ((store (w 0)).length+bits.length+1)^3 :=
    Nat.pow_le_pow_left (by omega) 3
  have lookupBig:=lookupLimit.trans (Nat.mul_le_mul_left 100 power)
  have linear : (store (w 0)).length+bits.length+1 ≤ ((store (w 0)).length+bits.length+1)^3 :=
    Nat.le_self_pow (by decide) _
  change _ ≤ 200*((store (w 0)).length+bits.length+1)^3
  omega

end Counting.External.MatchingInputValidation
