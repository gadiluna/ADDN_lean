import Counting.StackRealizabilityReachLift

namespace Counting.StackMachine.RealizabilityCheck
open Routine EncodingPrograms
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

def moveFlag (source target : Fin (registers+2)) : Routine registers:=
  branchRoutine source (pushBit target true) (pushBit target false)

theorem moveFlag_executes (source target : Fin (registers+2)) (different : source≠target)
    (store : Store registers) (bit : Bool) (tail : List Bool) (contents : store source=bit::tail) :
    Executes (moveFlag source target) store 2
      (Function.update (Function.update store source tail) target (bit::store target)):=by
  have push:=pushBit_executes target bit (Function.update store source tail)
  rw [Function.update_of_ne different.symm] at push
  cases bit
  · exact branch_executes_false source _ _ store _ tail 1 contents push
  · exact branch_executes_true source _ _ store _ tail 1 contents push

def reachTargetSeenRoles : Fin 7 ↪ Fin 17:=⟨![1,14,5,8,9,10,11],by decide⟩

def reachTarget : Routine 15:=sequence (ofProgram (ListPrograms.copyProgram 14 14 4 12))
  (sequence (ofProgram (ListPrograms.copyProgram 14 2 13 12))
    (sequence (bitLookup 10 reachTargetSeenRoles)
      (sequence reachLoop17 (sequence (moveFlag 5 16)
        (sequence (clear 3) (sequence (clear 4) (pushBit 14 true)))))))

def reachTargetValue (store : Store 15) : Bool:=
  reachFold (store 0) (store 1) (store 2).length 0 (store 14).length (store 2).length
    (RealizabilityVerifier.BitGraph.bitAt (store 1) (store 14).length)

def reachTargetStore (store : Store 15) : Store 15:=
  Function.update (Function.update store 16 (reachTargetValue store::store 16)) 14 (true::store 14)

theorem reachTarget_executes (store : Store 15)
    (e3 : store 3=[]) (e4 : store 4=[]) (e5 : store 5=[]) (e6 : store 6=[]) (e7 : store 7=[])
    (e9 : store 9=[]) (e10 : store 10=[]) (e11 : store 11=[]) (e12 : store 12=[]) (e13 : store 13=[]) :
    ∃ time ≤ 1000*((store 0).length+(store 1).length+(store 2).length+(store 14).length+1)^3,
      Executes reachTarget store time (reachTargetStore store):=by
  have first:=copy_executes 14 14 4 12 (by decide) (by decide) (by decide) store e12
  rw [e4,List.append_nil] at first
  let withIndex:=Function.update store 4 (store 14)
  have second:=copy_executes 14 2 13 12 (by decide) (by decide) (by decide) withIndex
    (by simp [withIndex,e12])
  have widthAt : withIndex 2=store 2:=by simp [withIndex]
  have counterAt : withIndex 13=[]:=by simp [withIndex,e13]
  rw [widthAt,counterAt,List.append_nil] at second
  let prepared:=Function.update withIndex 13 (store 2)
  let initial:=RealizabilityVerifier.BitGraph.bitAt (store 1) (store 14).length
  obtain ⟨readTime,readBound,reading⟩:=bitLookup_executes 10 reachTargetSeenRoles prepared
    (by simp [prepared,withIndex,reachTargetSeenRoles,e9])
    (by simp [prepared,withIndex,reachTargetSeenRoles,e10])
    (by simp [prepared,withIndex,reachTargetSeenRoles,e11])
  change readTime ≤ 6*(prepared 1).length+7*(prepared 14).length+16 at readBound
  have seenAt : prepared 1=store 1:=by simp [prepared,withIndex]
  have targetAt : prepared 14=store 14:=by simp [prepared,withIndex]
  rw [seenAt,targetAt] at readBound
  change Executes (bitLookup 10 reachTargetSeenRoles) prepared readTime
    (Function.update prepared 5 (RealizabilityVerifier.BitGraph.bitAt (prepared 1) (prepared 14).length::prepared 5)) at reading
  have initialStore : Function.update prepared 5
      (RealizabilityVerifier.BitGraph.bitAt (prepared 1) (prepared 14).length::prepared 5)=
        Function.update prepared 5 [initial]:=by simp [prepared,withIndex,initial,e5]
  rw [initialStore] at reading
  let read:=Function.update prepared 5 [initial]
  obtain ⟨loopTime,loopBound,loopRun⟩:=reachLoop17_executes read initial [] (store 2)
    (by simp [read]) (by simp [read,prepared])
    (by simp [read,prepared,withIndex,e6]) (by simp [read,prepared,withIndex,e7])
    (by simp [read,prepared,withIndex,e9]) (by simp [read,prepared,withIndex,e10])
    (by simp [read,prepared,withIndex,e11]) (by simp [read,prepared,withIndex,e12])
  let scanned:=reachLoop17Store read initial [] (store 2)
  have valueAt : scanned 5=[reachTargetValue store]:=by
    simp [scanned,reachLoop17Store,read,prepared,withIndex,reachTargetValue,initial,e3]
  have moving:=moveFlag_executes (5:Fin 17) 16 (by decide) scanned (reachTargetValue store) [] valueAt
  let emitted:=Function.update (Function.update scanned 5 []) 16 (reachTargetValue store::scanned 16)
  have clearSource:=clear_executes (3:Fin 17) emitted
  have sourceAt : emitted 3=List.replicate (store 2).length true:=by
    simp [emitted,scanned,reachLoop17Store,read,prepared,withIndex,e3]
  rw [sourceAt,List.length_replicate] at clearSource
  let noSource:=Function.update emitted 3 []
  have clearArc:=clear_executes (4:Fin 17) noSource
  have arcLength : (noSource 4).length=(store 2).length*(store 2).length+(store 14).length:=by
    simp [noSource,emitted,scanned,reachLoop17Store,read,prepared,withIndex]
  rw [arcLength] at clearArc
  let cleaned:=Function.update noSource 4 []
  have increment:=pushBit_executes (14:Fin 17) true cleaned
  have oldTarget : cleaned 14=store 14:=by
    simp [cleaned,noSource,emitted,scanned,reachLoop17Store,read,prepared,withIndex]
  rw [oldTarget] at increment
  have final : Function.update cleaned 14 (true::store 14)=reachTargetStore store:=by
    funext r
    fin_cases r <;> simp [cleaned,noSource,emitted,scanned,reachLoop17Store,read,prepared,withIndex,
      reachTargetStore,e3,e4,e5,e13]
  rw [final] at increment
  let S:=(store 0).length+(store 1).length+(store 2).length+(store 14).length+1
  have positive : 1 ≤ S:=by dsimp only [S];omega
  have width : (store 2).length ≤ S:=by dsimp only [S];omega
  have square : (store 2).length*((store 2).length+1) ≤ 2*S^2:=by
    have product:=Nat.mul_le_mul width (show (store 2).length+1 ≤ 2*S by omega)
    have same : S*(2*S)=2*S^2:=by ring
    omega
  have linearSquare : S ≤ S^2:=Nat.le_self_pow (by decide) _
  have loopSize : (read 0).length+(read 1).length+(read 2).length+(read 3).length+(read 4).length+1+
      (store 2).length*((read 2).length+1) ≤ 3*S^2:=by
    simp only [read,prepared,withIndex,Function.update_of_ne (by decide : (0:Fin 17)≠5),
      Function.update_of_ne (by decide : (0:Fin 17)≠13),Function.update_of_ne (by decide : (0:Fin 17)≠4),
      Function.update_of_ne (by decide : (1:Fin 17)≠5),Function.update_of_ne (by decide : (1:Fin 17)≠13),
      Function.update_of_ne (by decide : (1:Fin 17)≠4),Function.update_of_ne (by decide : (2:Fin 17)≠5),
      Function.update_of_ne (by decide : (2:Fin 17)≠13),Function.update_of_ne (by decide : (2:Fin 17)≠4),
      Function.update_of_ne (by decide : (3:Fin 17)≠5),Function.update_of_ne (by decide : (3:Fin 17)≠13),
      Function.update_of_ne (by decide : (3:Fin 17)≠4),Function.update_of_ne (by decide : (4:Fin 17)≠5),
      Function.update_of_ne (by decide : (4:Fin 17)≠13),Function.update_self,e3,List.length_nil,Nat.add_zero]
    change S+(store 2).length*((store 2).length+1) ≤ _
    omega
  have loopLimit : loopTime ≤ 180*S^3+2*S+1:=by
    have bound : loopTime ≤ S*(60*(3*S^2)+2)+1:=by
      apply loopBound.trans
      exact Nat.add_le_add_right (Nat.mul_le_mul width (Nat.add_le_add_right (Nat.mul_le_mul_left _ loopSize) 2)) 1
    have expansion (x : Nat) : x*(60*(3*x^2)+2)+1=180*x^3+2*x+1:=by ring
    exact expansion S ▸ bound
  have squareCube : S^2 ≤ S^3:=Nat.pow_le_pow_right positive (by decide)
  have linearCube : S ≤ S^3:=Nat.le_self_pow (by decide) _
  have oneCube : 1 ≤ S^3:=Nat.one_le_pow _ _ positive
  have widthSquare : (store 2).length*(store 2).length ≤ S^2:=by simpa only [pow_two] using Nat.mul_le_mul width width
  exact ⟨_,by change _ ≤ 1000*S^3;dsimp only [S] at loopLimit squareCube linearCube oneCube widthSquare ⊢;omega,
    first.sequence (second.sequence (reading.sequence (loopRun.sequence
      (moving.sequence (clearSource.sequence (clearArc.sequence increment))))))⟩

end Counting.StackMachine.RealizabilityCheck
