import Counting.ExternalCoverIndex
import Counting.StackScaleLength
import Counting.StackEmitNatural

namespace Counting.External.CoverMachine
open StackMachine StackMachine.Routine StackMachine.EncodingPrograms SATVerification MatchingMachine
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 900000

def shiftedNaturalPositions : Fin 5 ↪ Fin 32 := ⟨![26,21,29,30,20],by decide⟩
def shiftedNaturalRoles (extra : Nat) (w : SATWorkspace extra) : PowerWorkspace (extra+27) := shiftedNaturalPositions.trans w

def readShifted (extra : Nat) (w : SATWorkspace extra) (shift : Nat) : Routine (extra+30) :=
  sequence (readCoverIndex extra w)
    (sequence (scaleLength (extra+29) (w 17) (w 26) (w 20) shift)
      (sequence (emitNatural (extra+27) (shiftedNaturalRoles extra w)) (clear (w 26))))

def shiftedScratch : List (Fin 32) := coverIndexScratch++[20,29,30]

theorem readShifted_executes (extra : Nat) (w : SATWorkspace extra) (shift : Nat) (shiftBound : shift≤2)
    (store : Fin (extra+32) → List Bool) (index : Nat) (accepted : Bool) (suffix tail : List Bool)
    (source : store (w 0)=Encoding.natural.encode index++suffix)
    (status : store (w 1)=accepted::tail) (fits : index≤(store (w 17)).length)
    (empty : ∀ i∈shiftedScratch,store (w i)=[]) :
    ∃ time ≤ 1000*((store (w 0)).length+(store (w 17)).length+1)^3,
      Executes (readShifted extra w shift) store time
        (Function.update (Function.update store (w 0) suffix) (w 21)
          (Encoding.natural.encode (shift*(store (w 17)).length+index)++store (w 21))) := by
  let q := (store (w 17)).length
  let value := shift*q+index
  obtain ⟨readTime,readBound,reading⟩ := readCoverIndex_executes extra w store index accepted suffix tail source status fits
    (fun i mem=>empty i (by simp only [shiftedScratch,List.mem_append];exact Or.inl mem))
  let read := Function.update (Function.update store (w 0) suffix) (w 26) (List.replicate index true)
  have scaling := scaleLength_executes (extra+29) (w 17) (w 26) (w 20)
    (by simp [w.injective.eq_iff]) (by simp [w.injective.eq_iff]) (by simp [w.injective.eq_iff]) shift read
    (by simp [read,w.injective.eq_iff,empty,shiftedScratch])
  let scaled := Function.update (Function.update store (w 0) suffix) (w 26) (List.replicate value true)
  have scaleResult : Function.update read (w 26) (List.replicate (shift*(read (w 17)).length) true++read (w 26))=scaled := by
    simp [read,scaled,w.injective.eq_iff,value,q]
  rw [scaleResult] at scaling
  have qeq : (read (w 17)).length=q := by simp [read,q,w.injective.eq_iff]
  rw [qeq] at scaling
  obtain ⟨emitTime,emitBound,emitting⟩ := emitNatural_executes (extra+27) (shiftedNaturalRoles extra w) scaled
    (by simp [shiftedNaturalRoles,shiftedNaturalPositions,scaled,w.injective.eq_iff,empty,shiftedScratch])
    (by simp [shiftedNaturalRoles,shiftedNaturalPositions,scaled,w.injective.eq_iff,empty,shiftedScratch])
    (by simp [shiftedNaturalRoles,shiftedNaturalPositions,scaled,w.injective.eq_iff,empty,shiftedScratch])
  let emitted := Function.update scaled (w 21) (Encoding.natural.encode value++store (w 21))
  have emitAs : Executes (emitNatural (extra+27) (shiftedNaturalRoles extra w)) scaled emitTime emitted := by
    simpa [shiftedNaturalRoles,shiftedNaturalPositions,scaled,emitted,w.injective.eq_iff] using emitting
  have clearing := clear_executes (w 26) emitted
  have size : (emitted (w 26)).length=value := by simp [emitted,scaled,w.injective.eq_iff]
  rw [size] at clearing
  have final : Function.update emitted (w 26) []=
      Function.update (Function.update store (w 0) suffix) (w 21) (Encoding.natural.encode value++store (w 21)) := by
    funext r
    by_cases e : r=w 26
    · subst r;simp [w.injective.eq_iff,empty,shiftedScratch,coverIndexScratch]
    · simp [emitted,scaled,e,Function.update_apply]
  rw [final] at clearing
  refine ⟨readTime+1+(shift*(5*q+3)+1+(emitTime+1+(value+1))),?_,reading.sequence (scaling.sequence (emitAs.sequence clearing))⟩
  have emitLimit : emitTime≤20*(value+1)^2 := by
    simpa [shiftedNaturalRoles,shiftedNaturalPositions,scaled,w.injective.eq_iff] using emitBound
  let S := (store (w 0)).length+q+1
  have valueBound : value≤3*q := by dsimp [value,q];nlinarith
  have qBound : q≤S := by dsimp [S];omega
  have valuePower : (value+1)^2≤9*S^2 := by
    have linear : value+1≤3*S := by dsimp [S];omega
    have power := Nat.pow_le_pow_left linear 2
    nlinarith
  have square : S^2≤S^3 := Nat.pow_le_pow_right (by dsimp [S];omega) (by decide)
  have linear : S≤S^3 := Nat.le_self_pow (by decide) S
  have positive : 1≤S^3 := Nat.one_le_pow _ _ (by dsimp [S];omega)
  change readTime≤200*S^3 at readBound
  change _≤1000*S^3
  have scalingBound : shift*(5*q+3)≤10*q+6 := by nlinarith
  omega

end Counting.External.CoverMachine
