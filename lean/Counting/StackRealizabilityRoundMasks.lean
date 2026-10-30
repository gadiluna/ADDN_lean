import Counting.StackRealizabilityRoundPrepare

namespace Counting.StackMachine.RealizabilityCheck
open Routine
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000

def roundMaskRoles : Fin 30 ↪ Fin 100 := ⟨![0,85,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,86,18,19,87,21,83,84,24,25,26,88,89,90],by decide⟩
def roundMasks : Routine 98 := mapRegisters roundMaskRoles maskSlots

def roundMasksData (data : Fin 20→List Bool) (nodes : List Executable.Node) (round : Nat) : Fin 20→List Bool :=
  Function.update (Function.update (Function.update (Function.update (Function.update data
    6 (Encoding.sequence Encoding.node nodes)) 7 (List.replicate (nodes.length+1) true))
    8 (nodes.map (fun node=>decide (node.level=round))++[false]))
    9 (nodes.map (fun node=>decide (node.level=round+1))++[false]))
    10 (nodes.map (fun node=>decide (0<node.degree))++[false])

theorem roundMasksFile (data : Fin 20→List Bool) (nodes : List Executable.Node) (round : Nat) :
    roundFile (roundMasksData data nodes round)=
      Function.update (Function.update (Function.update (Function.update (Function.update (roundFile data)
        86 (Encoding.sequence Encoding.node nodes)) 87 (List.replicate (nodes.length+1) true))
        88 (nodes.map (fun node=>decide (node.level=round))++[false]))
        89 (nodes.map (fun node=>decide (node.level=round+1))++[false]))
        90 (nodes.map (fun node=>decide (0<node.degree))++[false]) := by
  change _=Function.update (Function.update (Function.update (Function.update (Function.update (roundFile data)
        (roundContext 6) _) (roundContext 7) _) (roundContext 8) _) (roundContext 9) _) (roundContext 10) _
  rw [roundFile_update,roundFile_update,roundFile_update,roundFile_update,roundFile_update]
  rfl

theorem roundMasks_executes (data : Fin 20→List Bool) (nodes : List Executable.Node) (round : Nat)
    (accepted : Bool) (tail : List Bool) (status : data 5=accepted::tail)
    (input : data 6=(Encoding.list Encoding.node).encode nodes)
    (old : data 3=round.bits) (next : data 4=(round+1).bits)
    (e7 : data 7=[]) (e8 : data 8=[]) (e9 : data 9=[]) (e10 : data 10=[]) :
    ∃ time ≤ 12000*((data 6).length+round.size+(round+1).size+1)^5,
      Executes roundMasks (roundFile data) time (roundFile (roundMasksData data nodes round)) := by
  let localStore : Store 28 := roundFile data ∘ roundMaskRoles
  have work (r : Fin 30) (small : r.val<17) (different : r≠1) : localStore r=[] := by
    fin_cases r <;> simp_all [localStore,roundFile,roundMaskRoles]
  obtain ⟨time,bound,run⟩ := maskSlots_executes localStore accepted tail
    (by simp [localStore,roundFile,roundMaskRoles,status]) work
    (by simp [localStore,roundFile,roundMaskRoles]) (by simp [localStore,roundFile,roundMaskRoles])
    (by simp [localStore,roundFile,roundMaskRoles,e7]) (by simp [localStore,roundFile,roundMaskRoles])
    (by simp [localStore,roundFile,roundMaskRoles]) (by simp [localStore,roundFile,roundMaskRoles])
    (by simp [localStore,roundFile,roundMaskRoles]) (by simp [localStore,roundFile,roundMaskRoles,e8])
    (by simp [localStore,roundFile,roundMaskRoles,e9]) (by simp [localStore,roundFile,roundMaskRoles,e10])
    nodes [] (by simp [localStore,roundFile,roundMaskRoles,input]) round (round+1)
    (by simp [localStore,roundFile,roundMaskRoles,old]) (by simp [localStore,roundFile,roundMaskRoles,next])
  refine ⟨time,by simpa [localStore,roundFile,roundMaskRoles] using bound,?_⟩
  apply relocate_executes_frame maskSlots roundMaskRoles (roundFile data) _ localStore _ time rfl _ _ run
  · intro r
    fin_cases r <;> simp [maskSlotsStore,localStore,roundFile,roundMaskRoles,roundMasksData]
  · intro r outside
    have n86 : r≠86 := by intro same;subst r;exact outside 17 rfl
    have n87 : r≠87 := by intro same;subst r;exact outside 20 rfl
    have n88 : r≠88 := by intro same;subst r;exact outside 27 rfl
    have n89 : r≠89 := by intro same;subst r;exact outside 28 rfl
    have n90 : r≠90 := by intro same;subst r;exact outside 29 rfl
    rw [roundMasksFile]
    simp [n86,n87,n88,n89,n90]

end Counting.StackMachine.RealizabilityCheck
