import Counting.StackNaturalPowerAccumulate
import Counting.ExternalCoverIndex
import Counting.ExternalMatchingGeneratorLayout

namespace Counting.External.CoefficientMachine
open StackMachine StackMachine.Routine CoverMachine MatchingMachine
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000

abbrev Workspace (extra : Nat) := GeneratorWorkspace extra

def powerSumPositions : Fin 18 ↪ Fin 64 :=
  ⟨![52,53,2,3,4,5,6,7,8,9,10,11,12,26,20,55,29,30],by decide⟩
def Workspace.powerSum (w : Workspace extra) : NaturalPower.SumWorkspace (extra+46) := powerSumPositions.trans w

def atomScratch : List (Fin 64) := [2,3,4,5,6,7,8,9,10,11,12,18,19,20,26,28,29,30,53]

def coefficientAtom (extra : Nat) (w : Workspace extra) : Routine (extra+62) :=
  sequence (readCoverIndex (extra+32) w.literal.reader) (NaturalPower.accumulatePower (extra+46) w.powerSum)

def atomCost (sourceLength universeLength baseLength sumLength exponent : Nat) :=
  200*(sourceLength+universeLength+1)^3+1+NaturalPower.accumulatePowerCost baseLength sumLength exponent

/-- Consume one canonical, bounded coordinate and add its base power to
the binary coefficient accumulator. No population-sized value is unary. -/
theorem coefficientAtom_executes (extra : Nat) (w : Workspace extra) (store : Fin (extra+64) → List Bool)
    (exponent : Nat) (accepted : Bool) (suffix tail : List Bool)
    (source : store (w 0)=Encoding.natural.encode exponent++suffix)
    (status : store (w 1)=accepted::tail) (fits : exponent ≤ (store (w 17)).length)
    (empty : ∀ i∈atomScratch,store (w i)=[]) :
    ∃ time ≤ atomCost (store (w 0)).length (store (w 17)).length (store (w 52)).length (store (w 55)).length exponent,
      Executes (coefficientAtom extra w) store time
        (Function.update (Function.update store (w 0) suffix) (w 55)
          (Encoding.value (store (w 55))+Encoding.value (store (w 52))^exponent).bits) := by
  have readerEmpty (i : Fin 32) (member : i∈coverIndexScratch) : store (w.literal.reader i)=[] := by
    simp only [coverIndexScratch,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    all_goals simpa [GeneratorWorkspace.literal,LiteralWorkspace.reader,literalPositions] using empty _ (by simp [atomScratch])
  obtain ⟨readTime,readBound,reading⟩:=readCoverIndex_executes (extra+32) w.literal.reader store exponent accepted suffix tail source status fits readerEmpty
  let read:=Function.update (Function.update store (w 0) suffix) (w 26) (List.replicate exponent true)
  change Executes (readCoverIndex (extra+32) w.literal.reader) store readTime read at reading
  have powerEmpty (i : Fin 18) (n0 : i≠0) (n13 : i≠13) (n15 : i≠15) : read (w.powerSum i)=[] := by
    fin_cases i
    all_goals first | contradiction | simp [Workspace.powerSum,powerSumPositions,read,w.injective.eq_iff,empty,atomScratch]
  obtain ⟨powerTime,powerBound,powering⟩:=NaturalPower.accumulatePower_executes (extra+46) w.powerSum read exponent
    (by simp [Workspace.powerSum,powerSumPositions,read]) powerEmpty
  have baseAt : read (w.powerSum 0)=store (w 52) := by simp [Workspace.powerSum,powerSumPositions,read,w.injective.eq_iff]
  have sumAt : read (w.powerSum 15)=store (w 55) := by simp [Workspace.powerSum,powerSumPositions,read,w.injective.eq_iff]
  rw [baseAt,sumAt] at powerBound powering
  change Executes (NaturalPower.accumulatePower (extra+46) w.powerSum) read powerTime
    (Function.update (Function.update read (w 26) []) (w 55)
      (Encoding.value (store (w 55))+Encoding.value (store (w 52))^exponent).bits) at powering
  have final : Function.update (Function.update read (w 26) []) (w 55)
      (Encoding.value (store (w 55))+Encoding.value (store (w 52))^exponent).bits=
      Function.update (Function.update store (w 0) suffix) (w 55)
      (Encoding.value (store (w 55))+Encoding.value (store (w 52))^exponent).bits := by
    funext r
    by_cases e26 : r=w 26
    · subst r;simp [w.injective.eq_iff,empty,atomScratch]
    · simp [read,Function.update_apply,e26]
  rw [final] at powering
  change readTime ≤ 200*((store (w 0)).length+(store (w 17)).length+1)^3 at readBound
  exact ⟨readTime+1+powerTime,by unfold atomCost;omega,reading.sequence powering⟩

end Counting.External.CoefficientMachine
