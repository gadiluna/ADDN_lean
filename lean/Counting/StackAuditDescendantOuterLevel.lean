import Counting.StackAuditDescendantPreserving

namespace Counting.StackMachine.AuditDescendant
open Routine
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000

def outerLevelRoles : Fin 40 ↪ Fin 48 :=
  ⟨fun r=>if r=34 then 40 else ⟨r.val,by omega⟩,by decide⟩

def outerLevel : Routine 46 := sequence (ofProgram (ListPrograms.copyProgram 45 46 17 0))
  (sequence (relocate readTable checkRoles)
    (sequence (ofProgram (ListPrograms.copyProgram 45 43 18 0))
      (sequence (relocate levelTest outerLevelRoles) (sequence (clear 17) (clear 30)))))

/-- Read the outer candidate node's real level while preserving the
canonical table, structural index, last-level label and all external data. -/
theorem outerLevel_executes (store : Store 46) (vista : Executable.Vista)
    (index : Fin vista.nodes.size) (anchor : Nat)
    (source : store 46=(Encoding.array Encoding.node).encode vista.nodes)
    (indexAt : (store 43).length=index.val) (anchorAt : store 40=anchor.bits)
    (empty : ∀ r : Fin 48,r.val<29 ∨ r=30 ∨ r=35 → store r=[]) :
    ∃ time ≤ 12000*((store 46).length+anchor.size+1)^4,
      Executes outerLevel store time
        (Function.update store 35 [decide ((vista.node index.val).level=anchor)]) := by
  have a:=copy_executes 45 (46:Fin 48) 17 0 (by decide) (by decide) (by decide) store
    (empty 0 (by decide))
  rw [empty 17 (by decide),List.append_nil] at a
  let copied:=Function.update store 17 (store 46)
  let headerStore : Store 38:=copied ∘ checkRoles
  obtain ⟨headerTime,headerBound,b⟩:=readTable_executes headerStore vista.nodes
    (by simp [headerStore,copied,checkRoles,source])
    (by simp [headerStore,copied,checkRoles,empty]) (by
      intro r small different;fin_cases r <;> simp_all [headerStore,copied,checkRoles])
  let ready:=Function.update (Function.update copied 17 (Encoding.sequence Encoding.node vista.nodes.toList))
    30 (List.replicate vista.nodes.size true)
  have header : Executes (relocate readTable checkRoles) copied headerTime ready := by
    apply relocate_executes_frame _ checkRoles copied ready headerStore _ headerTime rfl _ _ b
    · intro r;fin_cases r <;> simp [ready,headerStore,checkRoles,tableReady]
    · intro r outside
      have n17:r≠17 := by intro same;subst r;exact outside 17 rfl
      have n30:r≠30 := by intro same;subst r;exact outside 30 rfl
      simp [ready,n17,n30]
  have c:=copy_executes 45 (43:Fin 48) 18 0 (by decide) (by decide) (by decide) ready
    (by simp [ready,copied,empty])
  have indexStill : ready 43=store 43 := by simp [ready,copied]
  have vacant : ready 18=[] := by simp [ready,copied,empty]
  rw [indexStill,vacant,List.append_nil,indexAt] at c
  let indexed:=Function.update ready 18 (store 43)
  let levelStore : Store 38:=indexed ∘ outerLevelRoles
  obtain ⟨levelTime,levelBound,d⟩:=levelTest_executes levelStore vista index anchor
    (by simp [levelStore,indexed,outerLevelRoles,ready])
    (by simpa [levelStore,indexed,outerLevelRoles] using indexAt)
    (by simp [levelStore,indexed,outerLevelRoles,ready,copied,anchorAt]) (by
      intro r small n17 n18 n24 n25
      fin_cases r <;> simp_all [levelStore,indexed,outerLevelRoles,ready,copied])
  have priorFlag : levelStore 35=[] := by simp [levelStore,indexed,outerLevelRoles,ready,copied,empty]
  rw [priorFlag] at d
  let checked:=Function.update ready 35 [decide ((vista.node index.val).level=anchor)]
  have checking : Executes (relocate levelTest outerLevelRoles) indexed levelTime checked := by
    apply relocate_executes_frame _ outerLevelRoles indexed checked levelStore _ levelTime rfl _ _ d
    · intro r;fin_cases r <;> simp [checked,levelStore,indexed,outerLevelRoles,ready,copied,empty]
    · intro r outside
      have n18:r≠18 := by intro same;subst r;exact outside 18 rfl
      have n35:r≠35 := by intro same;subst r;exact outside 35 rfl
      simp [checked,indexed,n18,n35]
  have e:=clear_executes (17:Fin 48) checked
  have table : checked 17=Encoding.sequence Encoding.node vista.nodes.toList := by simp [checked,ready]
  rw [table] at e
  let erased:=Function.update checked 17 []
  have f:=clear_executes (30:Fin 48) erased
  have count : erased 30=List.replicate vista.nodes.size true := by simp [erased,checked,ready]
  rw [count,List.length_replicate] at f
  have final : Function.update erased 30 []=
      Function.update store 35 [decide ((vista.node index.val).level=anchor)] := by
    funext r
    by_cases r17:r=17 <;> by_cases r30:r=30 <;> by_cases r35:r=35 <;>
      simp [erased,checked,ready,copied,r17,r30,r35,empty]
  rw [final] at f
  have bareBound : (Encoding.sequence Encoding.node vista.nodes.toList).length ≤ (store 46).length := by
    rw [source]
    change (Encoding.sequence Encoding.node vista.nodes.toList).length ≤
      (Encoding.natural.encode vista.nodes.size++Encoding.sequence Encoding.node vista.nodes.toList).length
    simp only [List.length_append];omega
  have nodeCount:=DagValidation.node_sequence_count_le vista.nodes.toList
  rw [Array.length_toList] at nodeCount
  have tableAt : (headerStore 17).length=(store 46).length := by simp [headerStore,copied,checkRoles]
  have bareAt : (levelStore 17).length=(Encoding.sequence Encoding.node vista.nodes.toList).length := by
    simp [levelStore,indexed,outerLevelRoles,ready]
  rw [tableAt] at headerBound
  rw [bareAt] at levelBound
  let K:=(store 46).length+anchor.size+1
  have positive : 1 ≤ K := by dsimp only [K];omega
  have headerLimit : headerTime ≤ 2000*K^4 := headerBound.trans
    (Nat.mul_le_mul_left _ ((Nat.pow_le_pow_left (by dsimp only [K];omega) 3).trans
      (Nat.pow_le_pow_right positive (by decide))))
  have levelLimit : levelTime ≤ 9000*K^4 := levelBound.trans
    (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by dsimp only [K];omega) 4))
  have linear : K ≤ K^4:=Nat.le_self_pow (by decide) _
  have one : 1 ≤ K^4:=Nat.one_le_pow _ _ positive
  have tableBound : (store 46).length ≤ K := by dsimp only [K];omega
  have inside:=index.isLt
  refine ⟨_,?_,a.sequence (header.sequence (c.sequence (checking.sequence (e.sequence f))))⟩
  change 5*(store 46).length+2+1+(headerTime+1+(5*index.val+2+1+
    (levelTime+1+((Encoding.sequence Encoding.node vista.nodes.toList).length+1+1+(vista.nodes.size+1))))) ≤ 12000*K^4
  omega

end Counting.StackMachine.AuditDescendant
