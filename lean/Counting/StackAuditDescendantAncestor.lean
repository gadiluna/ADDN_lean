import Counting.StackAuditDescendantAt

namespace Counting.StackMachine.AuditDescendant
open Routine
set_option backward.isDefEq.respectTransparency false

def ancestorRoles : Fin 32 ↪ Fin 40 :=
  ⟨fun r=>if r=30 then 35 else ⟨r.val,by omega⟩,by decide⟩

def runAncestor : Routine 38:=relocate AuditAscend.ancestorEquals ancestorRoles

theorem runAncestor_executes (store : Store 38) (vista : Executable.Vista)
    (index ancestor : Nat) (bits : List Bool)
    (source : store 17=Encoding.sequence Encoding.node vista.nodes.toList)
    (current : store 24=(index+1).bits) (target : store 29=(ancestor+1).bits)
    (counter : store 25=bits)
    (empty : ∀ r : Fin 40,r.val ≤ 28 → r≠17 → r≠24 → r≠25 → store r=[]) :
    ∃ time ≤ 200000000*((store 17).length+(index+1).size+bits.length+(ancestor+1).size+1)^5,
      Executes runAncestor store time
        (Function.update (Function.update (Function.update store 25 []) 24 []) 35
          (decide (Executable.ascend vista bits.length index=some ancestor)::store 35)) := by
  let localStore : Store 30:=store ∘ ancestorRoles
  obtain ⟨time,bound,run⟩:=AuditAscend.ancestorEquals_executes localStore vista (some index) (some ancestor)
    (by simp [localStore,ancestorRoles,source])
    (by simp [localStore,ancestorRoles,AuditAscend.indexCode,current])
    (by simp [localStore,ancestorRoles,AuditAscend.indexCode,target]) (by
      intro r small n17 n24 n25
      fin_cases r <;> simp_all [localStore,ancestorRoles]) bits
    (by simp [localStore,ancestorRoles,counter])
  simp only [Option.bind_some] at run
  let output:=Function.update (Function.update (Function.update store 25 []) 24 []) 35
    (decide (Executable.ascend vista bits.length index=some ancestor)::store 35)
  have relocated : Executes runAncestor store time output := by
    apply relocate_executes_frame AuditAscend.ancestorEquals ancestorRoles store output localStore
      (Function.update (Function.update (Function.update localStore 25 []) 24 []) 30
        (decide (Executable.ascend vista bits.length index=some ancestor)::localStore 30)) time rfl _ _ run
    · intro r
      fin_cases r <;> simp [output,localStore,ancestorRoles]
    · intro r outside
      have n24 : r≠24 := fun same=>outside 24 (by simpa [ancestorRoles] using same.symm)
      have n25 : r≠25 := fun same=>outside 25 (by simpa [ancestorRoles] using same.symm)
      have n35 : r≠35 := fun same=>outside 30 (by simpa [ancestorRoles] using same.symm)
      simp [output,n24,n25,n35]
  refine ⟨time,?_,relocated⟩
  simpa [localStore,ancestorRoles,AuditAscend.indexCode] using bound

end Counting.StackMachine.AuditDescendant
