import Counting.StackProtocolVistaCounts
import Counting.StackEncodingFrameStore

namespace Counting.StackMachine.ProtocolVista
open Routine EncodingPrograms
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

def allRootLeaders (vista : Executable.Vista) : Bool :=
  !(Executable.levelNodes vista 0).any (fun i=>!(vista.node i).leader)

def outputWord (vista : Executable.Vista) : List Bool :=
  Encoding.natural.encode (vista.node vista.bottom).level++[allRootLeaders vista]

def rootEqualityRoles : Fin 6 ↪ Fin 52 := ⟨![29,43,1,4,5,6],by decide⟩
abbrev compareRoots : Routine 50 := Compare.preservingEquality 46 rootEqualityRoles

theorem rootsEqual (vista : Executable.Vista) :
    decide (((Executable.levelNodes vista 0).filter (fun i=>(vista.node i).leader)).length=
      (Executable.levelNodes vista 0).length)=allRootLeaders vista := by
  apply Bool.eq_iff_iff.mpr
  simp [allRootLeaders,List.length_filter_eq_length_iff,List.any_eq_false]

theorem compareRoots_executes (vista : Executable.Vista) (depth : List Bool) :
    ∃ time≤ 12*(Encoding.vista.encode vista).length+13,
      Executes compareRoots
        (file vista depth (List.replicate (Executable.levelNodes vista 0).length true)
          (List.replicate ((Executable.levelNodes vista 0).filter (fun i=>(vista.node i).leader)).length true)) time
        (Function.update (file vista depth (List.replicate (Executable.levelNodes vista 0).length true)
          (List.replicate ((Executable.levelNodes vista 0).filter (fun i=>(vista.node i).leader)).length true)) 1
            [allRootLeaders vista,true]) := by
  let roots:=(Executable.levelNodes vista 0).length
  let leaders:=((Executable.levelNodes vista 0).filter (fun i=>(vista.node i).leader)).length
  let store:=file vista depth (List.replicate roots true) (List.replicate leaders true)
  have run:=Compare.preservingEquality_executes 46 rootEqualityRoles store rfl rfl rfl
  change Executes _ store (Compare.preservingCost (List.replicate leaders true) (List.replicate roots true))
    (Function.update store 1 [decide (List.replicate leaders true=List.replicate roots true),true]) at run
  simp only [List.replicate_inj,and_true,or_true] at run
  rw [rootsEqual] at run
  have bound:=Compare.preservingCost_le (List.replicate leaders true) (List.replicate roots true)
  simp only [List.length_replicate] at bound
  have leaderBound:leaders≤ roots:=List.length_filter_le _ _
  have rootsBound:roots≤ vista.nodes.size:= (List.length_filter_le _ _).trans_eq List.length_range
  have nodeBound:=Encoding.vista_nodes_le_length vista
  exact ⟨_,by omega,run⟩

abbrev emit (flag : Bool) : Routine 50 := sequence (clear 1)
  (sequence (pushBit 1 flag) (frameRoutine 49 42 1 51))

theorem emit_executes (vista : Executable.Vista) (depth : Nat) (roots leaders : List Bool) (flag : Bool) :
    ∃ output,
      Executes (emit flag) (file vista depth.bits roots leaders) (5*depth.size+9) output ∧
      output 1=Encoding.natural.encode depth++[flag] := by
  let start:=file vista depth.bits roots leaders
  have a:=clear_executes (1:Fin 52) start
  change Executes _ start 2 (Function.update start 1 []) at a
  let erased:=Function.update start 1 []
  have b:=pushBit_executes (1:Fin 52) flag erased
  change Executes _ erased 1 (Function.update erased 1 [flag]) at b
  let flagged:=Function.update erased 1 [flag]
  have c:=frame_executes_updates 49 (42:Fin 52) 1 51 (by decide) (by decide) (by decide) flagged
    (by simp [flagged,erased,start,file])
  have source:flagged 42=depth.bits := by simp [flagged,erased,start,file]
  have status:flagged 1=[flag] := by simp [flagged]
  rw [source,status] at c
  have run:=a.sequence (b.sequence c)
  rw [Encoding.bits_length] at run
  refine ⟨Function.update (Function.update flagged 42 []) 1 (Encoding.frame depth.bits++[flag]),?_,by simp [Encoding.natural]⟩
  convert run using 1
  omega

abbrev finishRoots : Routine 50 := branchRoutine 1 (emit true) (emit false)

theorem finishRoots_executes (vista : Executable.Vista) (depth : Nat) (roots leaders : List Bool) (flag : Bool) :
    ∃ output,
      Executes finishRoots (Function.update (file vista depth.bits roots leaders) 1 [flag,true])
        (5*depth.size+10) output ∧ output 1=Encoding.natural.encode depth++[flag] := by
  have popped:Function.update (Function.update (file vista depth.bits roots leaders) 1 [flag,true]) 1 [true]=
      file vista depth.bits roots leaders := by
    rw [Function.update_idem]
    exact Function.update_eq_self 1 _
  obtain ⟨output,run,result⟩:=emit_executes vista depth roots leaders flag
  cases flag with
  | false=>
    have branch:=branch_executes_false (1:Fin 52) (emit true) (emit false)
      (Function.update (file vista depth.bits roots leaders) 1 [false,true]) output [true] _ (by simp)
      (by rw [popped];exact run)
    exact ⟨output,by convert branch using 1;omega,result⟩
  | true=>
    have branch:=branch_executes_true (1:Fin 52) (emit true) (emit false)
      (Function.update (file vista depth.bits roots leaders) 1 [true,true]) output [true] _ (by simp)
      (by rw [popped];exact run)
    exact ⟨output,by convert branch using 1;omega,result⟩

end Counting.StackMachine.ProtocolVista
