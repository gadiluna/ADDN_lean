import Counting.StackRealizabilityGraphExpr
import Counting.StackRealizabilityBitLookup
import Counting.StackDagClean

namespace Counting.StackMachine.RealizabilityCheck
open Routine
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

def activeNewRoles : Fin 7 ↪ Fin 14:=⟨![0,3,5,9,10,11,12],by decide⟩
def activeOldRoles : Fin 7 ↪ Fin 14:=⟨![1,3,6,9,10,11,12],by decide⟩
def activeOutsideRoles : Fin 7 ↪ Fin 14:=⟨![2,3,7,9,10,11,12],by decide⟩
def activeFlagRegisters : Fin 3 → Fin 14:=![5,6,7]
def activeFlagCells : List (Fin 14):=[5,6,7]

def activeItem : Routine 12:=sequence (bitLookup 7 activeNewRoles)
  (sequence (bitLookup 7 activeOldRoles)
    (sequence (bitLookup 7 activeOutsideRoles)
      (sequence (GraphExpr.compile activeFlagRegisters 8 GraphExpr.active)
        (sequence (clearRegisters activeFlagCells) (pushBit 3 true)))))

def activeBit (newBits oldBits outsideBits : List Bool) (index : Nat) : Bool:=
  RealizabilityVerifier.BitGraph.bitAt newBits index ||
  RealizabilityVerifier.BitGraph.bitAt oldBits index ||
  RealizabilityVerifier.BitGraph.bitAt outsideBits index

def activeItemStore (store : Store 12) : Store 12:=
  Function.update (Function.update store 8
    (activeBit (store 0) (store 1) (store 2) (store 3).length::store 8)) 3 (true::store 3)

theorem activeItem_executes (store : Store 12)
    (e5 : store 5=[]) (e6 : store 6=[]) (e7 : store 7=[])
    (e10 : store 10=[]) (e11 : store 11=[]) (e12 : store 12=[]) :
    ∃ time ≤ 100*((store 0).length+(store 1).length+(store 2).length+(store 3).length+1),
      Executes activeItem store time (activeItemStore store):=by
  let a:=RealizabilityVerifier.BitGraph.bitAt (store 0) (store 3).length
  let b:=RealizabilityVerifier.BitGraph.bitAt (store 1) (store 3).length
  let c:=RealizabilityVerifier.BitGraph.bitAt (store 2) (store 3).length
  obtain ⟨ta,ba,ra⟩:=bitLookup_executes 7 activeNewRoles store e10 e11 e12
  change ta≤6*(store 0).length+7*(store 3).length+16 at ba
  change Executes (bitLookup 7 activeNewRoles) store ta (Function.update store 5 (a::store 5)) at ra
  rw [e5] at ra
  let sa:=Function.update store 5 [a]
  obtain ⟨tb,bb,rb⟩:=bitLookup_executes 7 activeOldRoles sa
    (by simp [sa,activeOldRoles,e10]) (by simp [sa,activeOldRoles,e11]) (by simp [sa,activeOldRoles,e12])
  change tb≤6*(sa 1).length+7*(sa 3).length+16 at bb
  change tb≤6*(store 1).length+7*(store 3).length+16 at bb
  change Executes (bitLookup 7 activeOldRoles) sa tb
    (Function.update sa 6 (RealizabilityVerifier.BitGraph.bitAt (sa 1) (sa 3).length::sa 6)) at rb
  have rbResult : Function.update sa 6 (RealizabilityVerifier.BitGraph.bitAt (sa 1) (sa 3).length::sa 6)=
      Function.update sa 6 [b]:=by simp [sa,b,e6]
  rw [rbResult] at rb
  let sb:=Function.update sa 6 [b]
  obtain ⟨tc,bc,rc⟩:=bitLookup_executes 7 activeOutsideRoles sb
    (by simp [sb,sa,activeOutsideRoles,e10]) (by simp [sb,sa,activeOutsideRoles,e11])
    (by simp [sb,sa,activeOutsideRoles,e12])
  change tc≤6*(sb 2).length+7*(sb 3).length+16 at bc
  have at2 : sb 2=store 2:=by simp [sb,sa]
  have at3 : sb 3=store 3:=by simp [sb,sa]
  rw [at2,at3] at bc
  change Executes (bitLookup 7 activeOutsideRoles) sb tc
    (Function.update sb 7 (RealizabilityVerifier.BitGraph.bitAt (sb 2) (sb 3).length::sb 7)) at rc
  have rcResult : Function.update sb 7 (RealizabilityVerifier.BitGraph.bitAt (sb 2) (sb 3).length::sb 7)=
      Function.update sb 7 [c]:=by simp [sb,sa,c,e7]
  rw [rcResult] at rc
  let sc:=Function.update sb 7 [c]
  have evaluate:=GraphExpr.compile_executes activeFlagRegisters 8
    (by intro i;fin_cases i <;> decide) GraphExpr.active ![a,b,c] sc (fun _=>[])
    (by intro i;fin_cases i <;> simp [activeFlagRegisters,sc,sb,sa])
  have outputAt : sc 8=store 8:=by simp [sc,sb,sa]
  rw [outputAt,GraphExpr.eval_active] at evaluate
  let calculated:=Function.update sc 8 ((a||b||c)::store 8)
  obtain ⟨cleanupTime,cleanupBound,cleanup⟩:=DagValidation.clear_selected_executes activeFlagCells calculated 1
    (by intro r member;simp only [activeFlagCells,List.mem_cons,List.not_mem_nil,or_false] at member
        rcases member with rfl|rfl|rfl <;> simp [calculated,sc,sb,sa])
  have final : clearedStore activeFlagCells calculated=Function.update store 8 ((a||b||c)::store 8):=by
    funext r
    fin_cases r <;> simp [clearedStore,activeFlagCells,calculated,sc,sb,sa,e5,e6,e7]
  rw [final] at cleanup
  let cleaned:=Function.update store 8 ((a||b||c)::store 8)
  have increment:=pushBit_executes (3:Fin 14) true cleaned
  have index : cleaned 3=store 3:=by simp [cleaned]
  rw [index] at increment
  change cleanupTime≤3*(1+2) at cleanupBound
  have execution:=ra.sequence (rb.sequence (rc.sequence (evaluate.sequence (cleanup.sequence increment))))
  change Executes activeItem store (ta+1+(tb+1+(tc+1+(22+1+(cleanupTime+1+1))))) _ at execution
  exact ⟨_,by omega,execution⟩

end Counting.StackMachine.RealizabilityCheck
