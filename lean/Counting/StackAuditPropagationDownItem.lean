import Counting.StackAuditPropagationLevelLoop
import Counting.StackBinaryPredecessor
import Counting.StackRoutineMove

namespace Counting.StackMachine.AuditPropagation
open Routine
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000

def downPredRoles : Binary.PredWorkspace 32 := ⟨![22,30,2,3,4,5,6,7],by decide⟩

abbrev downItem : Routine 38 := sequence (Binary.predecessor 32 downPredRoles)
  (sequence (ofProgram (ListPrograms.copyProgram 37 36 32 4))
    (sequence levelLoop (sequence (clear 18) (sequence (clear 22) (move 37 30 22 4)))))

def downItemBudget (vista : Executable.Vista) (r tableLength : Nat) (weights : Array Nat) : Nat :=
  levelLoopBudget vista r tableLength 0 vista.nodes.size weights+
    60*((r+1).size+1)+6*vista.nodes.size+(r+1).size+6*r.size+13

/-- One descending-level iteration pays for the binary predecessor, copies
the explicit node counter, scans every node and restores its work space. -/
theorem downItem_executes (store : Store 38) (accepted : Bool) (tail : List Bool)
    (status : store 1=accepted::tail)
    (work : ∀ i : Fin 40,i.val<17 → i≠1 → store i=[])
    (e18 : store 18=[]) (e19 : store 19=[]) (e20 : store 20=[]) (e21 : store 21=[])
    (e23 : store 23=[]) (e24 : store 24=[]) (e25 : store 25=[])
    (e26 : store 26=[]) (e30 : store 30=[]) (e31 : store 31=[]) (e32 : store 32=[])
    (e33 : store 33=[]) (e37 : store 37=[]) (e38 : store 38=[])
    (vista : Executable.Vista) (weights : Array Nat) (length : weights.size=vista.nodes.size)
    (nodeInput : store 34=Encoding.vista.encode vista)
    (table : store 17=Encoding.sequence Encoding.node vista.nodes.toList++Encoding.natural.encode vista.bottom)
    (weightInput : store 35=(Encoding.array Encoding.natural).encode weights)
    (nodeCount : store 36=List.replicate vista.nodes.size true)
    (r : Nat) (level : store 22=(r+1).bits) :
    ∃ time ≤ downItemBudget vista r (store 17).length weights,
      Executes downItem store time
        (Function.update (Function.update store 22 r.bits) 35
          ((Encoding.array Encoding.natural).encode (Executable.propagateLevel vista weights r))) := by
  obtain ⟨predTime,predBound,a⟩ := Binary.predecessor_executes 32 downPredRoles store (r+1)
    (by simpa [downPredRoles] using level) (by
      intro i member
      fin_cases i <;> simp_all [downPredRoles])
  simp only [Nat.add_sub_cancel] at a
  let previous := Function.update store 30 r.bits
  change Executes _ store predTime previous at a
  have b := copy_executes 37 (36:Fin 40) 32 4 (by decide) (by decide) (by decide) previous
    (by simp [previous,work])
  have sourceAt : previous 36=List.replicate vista.nodes.size true := by simp [previous,nodeCount]
  have emptyAt : previous 32=[] := by simp [previous,e32]
  rw [sourceAt,emptyAt,List.append_nil,List.length_replicate] at b
  let counted := Function.update previous 32 (List.replicate vista.nodes.size true)
  have countedWork (i : Fin 40) (small : i.val<17) (different : i≠1) : counted i=[] := by
    have n30 : i≠30 := by intro same;subst i;norm_num at small
    have n32 : i≠32 := by intro same;subst i;norm_num at small
    simp [counted,previous,n30,n32,work i small different]
  obtain ⟨scanTime,scanBound,c⟩ := levelLoop_executes counted accepted tail
    (by simp [counted,previous,status]) countedWork (by simp [counted,previous,e19])
    (by simp [counted,previous,e20]) (by simp [counted,previous,e21])
    (by simp [counted,previous,e23]) (by simp [counted,previous,e24]) (by simp [counted,previous,e25])
    (by simp [counted,previous,e26]) (by simp [counted,previous,e31]) (by simp [counted,previous,e33])
    (by simp [counted,previous,e37]) (by simp [counted,previous,e38]) vista weights length
    (by simp [counted,previous,nodeInput]) (by simp [counted,previous,table])
    (by simp [counted,previous,weightInput]) r 0 vista.nodes.size (by omega)
    (by simp [counted,previous,level]) (by simp [counted,previous]) (by simp [counted,previous,e18])
    (List.replicate vista.nodes.size true) (by simp [counted]) (by simp)
  let output := (Encoding.array Encoding.natural).encode (Executable.propagateLevel vista weights r)
  let scanned := Function.update (Function.update previous 18 (List.replicate vista.nodes.size true)) 35 output
  have cs : levelLoopStore counted vista r 0 vista.nodes.size weights=scanned := by
    funext i
    by_cases i18 : i=18 <;> by_cases i32 : i=32 <;> by_cases i35 : i=35 <;>
      simp [levelLoopStore,levelScan_full,scanned,counted,previous,output,i18,i32,i35,e32]
  rw [cs] at c
  have d := clear_executes (18:Fin 40) scanned
  have scanCount : scanned 18=List.replicate vista.nodes.size true := by simp [scanned]
  rw [scanCount,List.length_replicate] at d
  let cleared := Function.update previous 35 output
  have ds : Function.update scanned 18 []=cleared := by
    funext i
    by_cases i18 : i=18 <;> by_cases i35 : i=35 <;> simp [scanned,cleared,previous,i18,i35,e18]
  rw [ds] at d
  have e := clear_executes (22:Fin 40) cleared
  have oldLevel : cleared 22=(r+1).bits := by simp [cleared,previous,level]
  rw [oldLevel,Encoding.bits_length] at e
  let erased := Function.update cleared 22 []
  have f := move_executes 37 (30:Fin 40) 22 4 (by decide) (by decide) (by decide) erased
    (by simp [erased,cleared,previous,work])
  have source : erased 30=r.bits := by simp [erased,cleared,previous]
  have target : erased 22=[] := by simp [erased]
  rw [source,target,List.append_nil,Encoding.bits_length] at f
  have fs : Function.update (Function.update erased 22 r.bits) 30 []=
      Function.update (Function.update store 22 r.bits) 35 output := by
    funext i
    by_cases i22 : i=22 <;> by_cases i30 : i=30 <;> by_cases i35 : i=35 <;>
      simp [erased,cleared,previous,i22,i30,i35,e30]
  rw [fs] at f
  refine ⟨_,?_,a.sequence (b.sequence (c.sequence (d.sequence (e.sequence f))))⟩
  have sameTable : counted 17=store 17 := by simp [counted,previous]
  rw [sameTable] at scanBound
  unfold downItemBudget
  omega

end Counting.StackMachine.AuditPropagation
