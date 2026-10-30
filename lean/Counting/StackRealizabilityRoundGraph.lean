import Counting.StackRealizabilityRoundFile
import Counting.StackRealizabilityGraphCheckSpec

namespace Counting.StackMachine.RealizabilityCheck
open Routine EncodingPrograms
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000

def roundGraphRoles : Fin 42 ↪ Fin 100 := ⟨![89,88,93,90,91,92,94,95,87,85,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38,39,40,41],by decide⟩
def roundGraphTables (data : Fin 20→List Bool) : Fin 8→List Bool :=
  ![data 9,data 8,data 13,data 10,data 11,data 12,data 14,data 15]
def roundGraph : Routine 98 := mapRegisters roundGraphRoles graphCheckRoutine

theorem roundGraph_executes (data : Fin 20→List Bool) (accepted : Bool) (tail : List Bool)
    (status : data 5=accepted::tail) :
    ∃ time ≤ 30000000000*(graphSize (roundGraphTables data) (data 7))^12,
      Executes roundGraph (roundFile data) time
        (roundFile (Function.update data 5
          ((accepted && graphFieldsAnswer (roundGraphTables data) (data 7).length)::tail))) := by
  obtain ⟨time,bound,run⟩ := graphCheck_executes (roundGraphTables data) (data 7) accepted tail
  refine ⟨time,bound,?_⟩
  apply relocate_executes_frame graphCheckRoutine roundGraphRoles (roundFile data) _ _ _ time _ _ _ run
  · funext r
    fin_cases r <;> simp [roundFile,roundGraphRoles,graphFile,roundGraphTables,status]
  · intro r
    fin_cases r <;> simp [roundFile,roundGraphRoles,graphFile,roundGraphTables]
  · intro r outside
    have different : r≠85 := by intro same;subst r;exact outside 9 rfl
    rw [←roundFile_update]
    exact Function.update_of_ne different _ _

def roundGraphCompareRoles : Fin 6 ↪ Fin 100 := ⟨![82,0,2,3,4,5],by decide⟩
def roundGraphFlag : Routine 98 := sequence (pushBit 0 true)
  (sequence (differencePositive 94 roundGraphCompareRoles) (clear 0))

theorem roundGraphFlag_executes (data : Fin 20→List Bool) (order : Nat) (encoded : data 2=order.bits) :
    ∃ time ≤ 30*(order.size+1),
      Executes roundGraphFlag (roundFile data) time
        (Function.update (roundFile data) 2 [decide (1<order)]) := by
  have pushing := pushBit_executes (0:Fin 100) true (roundFile data)
  have empty0 : roundFile data 0=[] := by simp [roundFile]
  rw [empty0] at pushing
  let ready := Function.update (roundFile data) 0 [true]
  have comparing := differencePositive_executes 94 roundGraphCompareRoles ready order 1
    (by simp [ready,roundFile,roundGraphCompareRoles,encoded])
    (by simp [ready,roundGraphCompareRoles])
    (by simp [ready,roundFile,roundGraphCompareRoles])
    (by simp [ready,roundFile,roundGraphCompareRoles])
    (by simp [ready,roundFile,roundGraphCompareRoles])
  have positive : (0<order-1) ↔ 1<order := by omega
  have outAt : ready (roundGraphCompareRoles 2)=[] := by simp [ready,roundFile,roundGraphCompareRoles]
  simp only [positive,outAt] at comparing
  let flagged := Function.update ready 2 [decide (1<order)]
  have clearing := clear_executes (0:Fin 100) flagged
  have at0 : flagged 0=[true] := by simp [flagged,ready]
  rw [at0] at clearing
  have final : Function.update flagged 0 []=Function.update (roundFile data) 2 [decide (1<order)] := by
    simp [flagged,ready,Function.update_comm (by decide : (0:Fin 100)≠2),empty0]
  rw [final] at clearing
  have compareBound := Binary.preservingCompareCost_le order.bits (1:Nat).bits
  simp only [Encoding.bits_length] at compareBound
  have execution := pushing.sequence (comparing.sequence clearing)
  exact ⟨_,by norm_num at compareBound ⊢;omega,execution⟩

def roundConditionalGraph : Routine 98 := sequence roundGraphFlag (branchRoutine 2 roundGraph (skip 98))

theorem roundConditionalGraph_executes (data : Fin 20→List Bool) (order : Nat) (accepted : Bool)
    (tail : List Bool) (encoded : data 2=order.bits) (status : data 5=accepted::tail) :
    ∃ time ≤ 30000000000*(graphSize (roundGraphTables data) (data 7))^12+30*(order.size+1)+2,
      Executes roundConditionalGraph (roundFile data) time
        (roundFile (Function.update data 5
          ((accepted && (if 1<order then graphFieldsAnswer (roundGraphTables data) (data 7).length else true))::tail))) := by
  obtain ⟨flagTime,flagBound,flagRun⟩ := roundGraphFlag_executes data order encoded
  let ready := Function.update (roundFile data) 2 [decide (1<order)]
  have restored : Function.update ready 2 []=roundFile data := by
    simp [ready,roundFile]
  by_cases positive : 1<order
  · obtain ⟨graphTime,graphBound,graphRun⟩ := roundGraph_executes data accepted tail status
    have branched := branch_executes_true (2:Fin 100) roundGraph (skip 98) ready _ [] graphTime
      (by simp [ready,positive]) (by rw [restored];exact graphRun)
    have execution := flagRun.sequence branched
    simp only [if_pos positive]
    exact ⟨_,by omega,execution⟩
  · have branched := branch_executes_false (2:Fin 100) roundGraph (skip 98) ready (roundFile data) [] 0
      (by simp [ready,positive]) (by rw [restored];exact skip_executes _)
    have final : roundFile (Function.update data 5
        ((accepted && (if 1<order then graphFieldsAnswer (roundGraphTables data) (data 7).length else true))::tail))=
        roundFile data := by simp [positive,←status]
    rw [final]
    exact ⟨_,by omega,flagRun.sequence branched⟩

end Counting.StackMachine.RealizabilityCheck
