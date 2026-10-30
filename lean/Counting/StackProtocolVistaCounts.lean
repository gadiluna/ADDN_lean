import Counting.StackProtocolVistaTable

namespace Counting.StackMachine.ProtocolVista
open Routine
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

def countRoles : Fin 36 ↪ Fin 52 :=
  ⟨fun r=>⟨r.val,by omega⟩,by intro a b same;exact Fin.ext (congrArg (fun r:Fin 52=>r.val) same)⟩

abbrev count (mode : AuditPrefix.HeaderMode) : Routine 50 := relocate (AuditPrefix.countAll mode) countRoles

theorem count_executes (vista : Executable.Vista) (mode : AuditPrefix.HeaderMode) (depth roots : List Bool) :
    ∃ time≤ 20000*((Encoding.vista.encode vista).length+1)^5,
      Executes (count mode) (file vista depth roots []) time
        (file vista depth roots (List.replicate (AuditPrefix.countRange vista mode 0 0 0 vista.nodes.size) true)) := by
  let store:=file vista depth roots []
  let localStore:Store 34:=store ∘ countRoles
  obtain ⟨time,bounded,run⟩:=AuditPrefix.countAll_executes mode vista localStore true [] rfl
    (by intro r small different;fin_cases r <;> simp_all [localStore,store,file,countRoles])
    rfl rfl rfl rfl rfl rfl rfl (Encoding.natural.encode vista.bottom) rfl rfl 0 0 rfl rfl
  have vacant:localStore 29=[] := rfl
  rw [vacant,List.append_nil] at run
  let amount:=AuditPrefix.countRange vista mode 0 0 0 vista.nodes.size
  have lifted:Executes (count mode) store time (file vista depth roots (List.replicate amount true)) := by
    apply relocate_executes_frame (AuditPrefix.countAll mode) countRoles _ _ _ _ time rfl _ _ run
    · intro r;fin_cases r <;> simp [localStore,store,file,countRoles,amount]
    · intro r outside
      have n29:r≠29 := by intro same;subst r;exact outside 29 rfl
      simp [store,file,n29]
  change time≤ 20000*((tableWord vista).length+Nat.size 0+Nat.size 0+1)^5 at bounded
  simp only [Nat.size_zero,Nat.add_zero] at bounded
  exact ⟨time,bounded.trans (Nat.mul_le_mul_left 20000
    (Nat.pow_le_pow_left (Nat.add_le_add_right (tableWord_length vista) 1) 5)),lifted⟩

abbrev saveRoots : Routine 50 := move 49 29 43 51

theorem saveRoots_executes (vista : Executable.Vista) (depth : List Bool) (roots : Nat) :
    Executes saveRoots (file vista depth [] (List.replicate roots true)) (6*roots+4)
      (file vista depth (List.replicate roots true) []) := by
  have run:=move_executes 49 (29:Fin 52) 43 51 (by decide) (by decide) (by decide)
    (file vista depth [] (List.replicate roots true)) rfl
  change Executes _ _ (6*(List.replicate roots true).length+4)
    (Function.update (Function.update (file vista depth [] (List.replicate roots true)) 43
      (List.replicate roots true++[])) 29 []) at run
  simp only [List.length_replicate,List.append_nil] at run
  have target:Function.update (Function.update (file vista depth [] (List.replicate roots true)) 43
      (List.replicate roots true)) 29 []=file vista depth (List.replicate roots true) [] := by
    funext r;fin_cases r <;> simp [file]
  rwa [target] at run

abbrev bothCounts : Routine 50 := sequence (count .level) (sequence saveRoots (count .leader))

theorem bothCounts_executes (vista : Executable.Vista) (depth : List Bool) :
    ∃ time≤ 41000*((Encoding.vista.encode vista).length+1)^5,
      Executes bothCounts (file vista depth [] []) time
        (file vista depth (List.replicate (Executable.levelNodes vista 0).length true)
          (List.replicate ((Executable.levelNodes vista 0).filter (fun i=>(vista.node i).leader)).length true)) := by
  obtain ⟨a,abound,arun⟩:=count_executes vista .level depth []
  rw [AuditPrefix.countRange_full_level] at arun
  have brun:=saveRoots_executes vista depth (Executable.levelNodes vista 0).length
  obtain ⟨c,cbound,crun⟩:=count_executes vista .leader depth (List.replicate (Executable.levelNodes vista 0).length true)
  rw [AuditPrefix.countRange_full_leaders] at crun
  have roots:(Executable.levelNodes vista 0).length≤ vista.nodes.size := by
    exact (List.length_filter_le _ _).trans_eq List.length_range
  have nodes:=Encoding.vista_nodes_le_length vista
  have linear:(Encoding.vista.encode vista).length+1≤ ((Encoding.vista.encode vista).length+1)^5:=
    Nat.le_self_pow (by decide) _
  exact ⟨_,by omega,arun.sequence (brun.sequence crun)⟩

end Counting.StackMachine.ProtocolVista
