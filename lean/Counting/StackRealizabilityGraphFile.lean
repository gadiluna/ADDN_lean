import Counting.StackRealizabilityGraphTables
import Counting.StackRealizabilityReachCheck
import Counting.StackEncodingRelabel

namespace Counting.StackMachine.RealizabilityCheck
open Routine
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

def graphFile (tables : Fin 8→List Bool) (width status arcs active : List Bool) : Store 40:=
  fun r=>if h : r.val<8 then tables ⟨r.val,h⟩ else if r=8 then width else if r=9 then status
    else if r=10 then arcs else if r=13 then active else []

def graphSize (tables : Fin 8→List Bool) (width : List Bool) : Nat:=
  (tables 0).length+(tables 1).length+(tables 2).length+(tables 3).length+
  (tables 4).length+(tables 5).length+(tables 6).length+(tables 7).length+width.length+1

def graphMatrixRoles : Fin 32 ↪ Fin 42:=⟨![0,1,2,3,4,5,6,7,12,14,15,16,
  17,18,19,20,21,22,23,24,25,26,27,28,29,11,30,31,32,8,10,33],by decide⟩
def graphActiveRoles : Fin 14 ↪ Fin 42:=⟨![0,1,2,12,8,13,14,15,16,11,17,18,19,20],by decide⟩
def graphReachRoles : Fin 24 ↪ Fin 42:=⟨![10,21,8,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,13,9,37,38,39,40],by decide⟩

def graphMatrixRoutine : Routine 40:=mapRegisters graphMatrixRoles arcMatrix
def graphActiveRoutine : Routine 40:=mapRegisters graphActiveRoles activeVector
def graphReachRoutine : Routine 40:=mapRegisters graphReachRoles reachCheckRoutine

theorem graphMatrix_executes (tables : Fin 8→List Bool) (width status : List Bool) :
    ∃ time ≤ 1000000*(graphSize tables width)^7,
      Executes graphMatrixRoutine (graphFile tables width status [] []) time
        (graphFile tables width status (arcTableValues tables width.length 0 0 width.length) []):=by
  let original:Store 30:=graphFile tables width status [] [] ∘ graphMatrixRoles
  have work : ArcWorkspaceEmpty original:=by
    intro r lo n25 n29
    fin_cases r <;> simp_all [original,graphFile,graphMatrixRoles]
  obtain ⟨time,bound,run⟩:=arcMatrix_executes original work
  have size : arcReadSize original+(original 29).length=graphSize tables width:=by
    simp [original,arcReadSize,graphSize,graphFile,graphMatrixRoles]
    omega
  rw [size] at bound
  have tableEq : arcTables original=tables:=by
    funext i
    fin_cases i <;> simp [arcTables,original,graphFile,graphMatrixRoles]
  have widthEq : original 29=width:=by simp [original,graphFile,graphMatrixRoles]
  rw [tableEq,widthEq] at run
  refine ⟨time,bound,?_⟩
  apply relocate_executes_frame arcMatrix graphMatrixRoles _ _ original _ time rfl _ _ run
  · intro r;fin_cases r <;> simp [original,graphFile,graphMatrixRoles]
  · intro r outside
    have n10 : r≠10:=by intro same;subst r;exact outside 30 rfl
    simp [graphFile,n10]

theorem graphActive_executes (tables : Fin 8→List Bool) (width status arcs : List Bool) :
    ∃ time ≤ 1000*(graphSize tables width)^2,
      Executes graphActiveRoutine (graphFile tables width status arcs []) time
        (graphFile tables width status arcs (activeValues (tables 0) (tables 1) (tables 2) 0 width.length)):=by
  let original:Store 12:=graphFile tables width status arcs [] ∘ graphActiveRoles
  obtain ⟨time,bound,run⟩:=activeVector_executes original
    (by simp [original,graphFile,graphActiveRoles]) (by simp [original,graphFile,graphActiveRoles])
    (by simp [original,graphFile,graphActiveRoles]) (by simp [original,graphFile,graphActiveRoles])
    (by simp [original,graphFile,graphActiveRoles]) (by simp [original,graphFile,graphActiveRoles])
    (by simp [original,graphFile,graphActiveRoles]) (by simp [original,graphFile,graphActiveRoles])
    (by simp [original,graphFile,graphActiveRoles])
  have originalSize : (original 0).length+(original 1).length+(original 2).length+(original 4).length+1≤
      graphSize tables width:=by simp [original,graphFile,graphActiveRoles,graphSize];omega
  refine ⟨time,bound.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left originalSize 2)),?_⟩
  apply relocate_executes_frame activeVector graphActiveRoles _ _ original _ time rfl _ _ run
  · intro r;fin_cases r <;> simp [original,graphFile,graphActiveRoles]
  · intro r outside
    have n13 : r≠13:=by intro same;subst r;exact outside 5 rfl
    simp [graphFile,n13]

theorem graphReach_executes (tables : Fin 8→List Bool) (width arcs active : List Bool)
    (accepted : Bool) (tail : List Bool) :
    ∃ time ≤ 7000000*(arcs.length+active.length+width.length+1)^6,
      Executes graphReachRoutine (graphFile tables width (accepted::tail) arcs active) time
        (graphFile tables width ((accepted && RealizabilityVerifier.BitGraph.check width.length arcs active)::tail)
          arcs active):=by
  let original:Store 22:=graphFile tables width (accepted::tail) arcs active ∘ graphReachRoles
  have empty : RowEmpty original:=by
    intro r n0 n2 n17 n18 n19 n23
    fin_cases r <;> simp_all [original,graphFile,graphReachRoles]
  obtain ⟨time,bound,run⟩:=reachCheck_executes original accepted tail
    (by simp [original,graphFile,graphReachRoles]) empty
    (by simp [original,graphFile,graphReachRoles]) (by simp [original,graphFile,graphReachRoles])
  have normalized : (original 0).length+(original 18).length+(original 2).length+1=
      arcs.length+active.length+width.length+1:=by simp [original,graphFile,graphReachRoles]
  rw [normalized] at bound
  refine ⟨time,bound,?_⟩
  apply relocate_executes_frame reachCheckRoutine graphReachRoles _ _ original _ time rfl _ _ run
  · intro r;fin_cases r <;> simp [original,graphFile,graphReachRoles]
  · intro r outside
    have n9 : r≠9:=by intro same;subst r;exact outside 19 rfl
    simp [graphFile,n9]

end Counting.StackMachine.RealizabilityCheck
