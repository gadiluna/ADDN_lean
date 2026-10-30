import Counting.StackRealizabilityBitLookup
import Counting.StackBooleanFold

namespace Counting.StackMachine.RealizabilityCheck
open Routine
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

def reachSeenRoles : Fin 7 ↪ Fin 14:=⟨![1,3,6,8,9,10,11],by decide⟩
def reachArcRoles : Fin 7 ↪ Fin 14:=⟨![0,4,7,8,9,10,11],by decide⟩

/-- One old vertex contributes a conjunction to one target's disjunction.
The arc index advances by the explicit unary row width, never by an encoded population. -/
def reachItem : Routine 12:=sequence (bitLookup 7 reachSeenRoles)
  (sequence (bitLookup 7 reachArcRoles)
    (sequence (BooleanFold.single .conjunction 6 7)
      (sequence (BooleanFold.single .disjunction 7 5)
        (sequence (pushBit 3 true) (ofProgram (ListPrograms.copyProgram 11 2 4 12))))))

def reachContribution (store : Store 12) : Bool:=
  RealizabilityVerifier.BitGraph.bitAt (store 1) (store 3).length &&
    RealizabilityVerifier.BitGraph.bitAt (store 0) (store 4).length

def reachItemStore (store : Store 12) (value : Bool) (tail : List Bool) : Store 12:=
  Function.update (Function.update (Function.update store 5 ((value || reachContribution store)::tail))
    3 (true::store 3)) 4 (store 2++store 4)

theorem reachItem_executes (store : Store 12) (value : Bool) (tail : List Bool)
    (accumulated : store 5=value::tail)
    (e6 : store 6=[]) (e7 : store 7=[])
    (e9 : store 9=[]) (e10 : store 10=[]) (e11 : store 11=[]) (e12 : store 12=[]) :
    ∃ time ≤ 60*((store 0).length+(store 1).length+(store 2).length+
        (store 3).length+(store 4).length+1),
      Executes reachItem store time (reachItemStore store value tail):=by
  let seen:=RealizabilityVerifier.BitGraph.bitAt (store 1) (store 3).length
  let arc:=RealizabilityVerifier.BitGraph.bitAt (store 0) (store 4).length
  obtain ⟨seenTime,seenBound,seenRun⟩:=bitLookup_executes 7 reachSeenRoles store e9 e10 e11
  change seenTime ≤ 6*(store 1).length+7*(store 3).length+16 at seenBound
  change Executes (bitLookup 7 reachSeenRoles) store seenTime (Function.update store 6 (seen::store 6)) at seenRun
  rw [e6] at seenRun
  let withSeen:=Function.update store 6 [seen]
  obtain ⟨arcTime,arcBound,arcRun⟩:=bitLookup_executes 7 reachArcRoles withSeen
    (by simp [withSeen,reachArcRoles,e9]) (by simp [withSeen,reachArcRoles,e10])
    (by simp [withSeen,reachArcRoles,e11])
  change arcTime ≤ 6*(withSeen 0).length+7*(withSeen 4).length+16 at arcBound
  have at0 : withSeen 0=store 0:=by simp [withSeen]
  have at4 : withSeen 4=store 4:=by simp [withSeen]
  rw [at0,at4] at arcBound
  change Executes (bitLookup 7 reachArcRoles) withSeen arcTime
    (Function.update withSeen 7 (RealizabilityVerifier.BitGraph.bitAt (withSeen 0) (withSeen 4).length::withSeen 7)) at arcRun
  have arcStore : Function.update withSeen 7
      (RealizabilityVerifier.BitGraph.bitAt (withSeen 0) (withSeen 4).length::withSeen 7)=
        Function.update withSeen 7 [arc]:=by simp [withSeen,arc,e7]
  rw [arcStore] at arcRun
  let read:=Function.update withSeen 7 [arc]
  have andRun:=BooleanFold.single_executes .conjunction (6:Fin 14) 7 (by decide) read seen arc [] []
    (by simp [read,withSeen]) (by simp [read])
  let joined:=BooleanFold.updated 6 7 read [] (arc && seen) []
  have orRun:=BooleanFold.single_executes .disjunction (7:Fin 14) 5 (by decide) joined (arc&&seen) value [] tail
    (by simp [joined,BooleanFold.updated])
    (by simp [joined,BooleanFold.updated,read,withSeen,accumulated])
  let folded:=BooleanFold.updated 7 5 joined [] (value || (arc&&seen)) tail
  have increment:=pushBit_executes (3:Fin 14) true folded
  have oldIndex : folded 3=store 3:=by simp [folded,joined,BooleanFold.updated,read,withSeen]
  rw [oldIndex] at increment
  let indexed:=Function.update folded 3 (true::store 3)
  have copy:=copy_executes 11 2 4 12 (by decide) (by decide) (by decide) indexed
    (by simp [indexed,folded,joined,BooleanFold.updated,read,withSeen,e12])
  have width : indexed 2=store 2:=by simp [indexed,folded,joined,BooleanFold.updated,read,withSeen]
  have index : indexed 4=store 4:=by simp [indexed,folded,joined,BooleanFold.updated,read,withSeen]
  rw [width,index] at copy
  have final : Function.update indexed 4 (store 2++store 4)=reachItemStore store value tail:=by
    funext r
    fin_cases r <;> simp [indexed,folded,joined,BooleanFold.updated,read,withSeen,
      reachItemStore,reachContribution,seen,arc,Bool.and_comm,e6,e7]
  rw [final] at copy
  exact ⟨_,by omega,seenRun.sequence (arcRun.sequence (andRun.sequence (orRun.sequence (increment.sequence copy))))⟩

end Counting.StackMachine.RealizabilityCheck
